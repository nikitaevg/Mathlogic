module Predicate.Checker
(
	Annotation(..),
	Rule(..),
	ErrorWithNum(..),
	Error(..),
	SubstRes(..),
	parseP
) where

import Predicate.Parser
import Predicate.Axioms
import Data.Maybe
import Data.List
import Data.List.Split
import qualified Data.Map as M
import qualified Data.MultiMap as MM
import qualified Data.Set as S

data Annotation = Conclusion {ith :: Expression, jth :: Expression, rule :: Rule} 
				  | Axiom Int | Assumption Int
				  | NotProven deriving (Show, Eq, Ord)

data Rule = MP | ForAll | ForOne deriving (Show, Eq, Ord)

data ErrorWithNum = Err {errorWN :: Error, number :: Int} deriving (Eq, Ord)
instance Show ErrorWithNum where
	show (Err error num) = "Вывод некорректен начиная с формулы номер " ++ (show num) ++ (show error)

data Error = NotFreeForSubst Term Expression Term
			| FreeForSubst Expression Term
			| FreeForSubstInAss Expression Term
			| NoProof deriving (Eq, Ord)

instance Show Error where
	show (NotFreeForSubst x y a) = ": терм " ++ (show x) ++ " не свободен для подстановки в формулу " ++ (show y) ++ " вместо переменной " ++ (show a) ++ "." 
	show (FreeForSubst x a) = ": переменная " ++ (show a) ++ " входит свободно в формулу " ++ (show x) ++ "."
	show (FreeForSubstInAss x a) = ": используется правило с квантором по переменной " ++ (show a) ++ ", входящей свободно в допущение " ++ (show x) ++ "."
	show _ = "."
addMaybe :: Maybe a -> Maybe a -> Maybe a
addMaybe (Just a) Nothing = Just a
addMaybe _ a = a

type PredMap = M.Map Predicate Expression
data SubstRes = Ok | NotCorrectSubst | NotEqual deriving (Show, Eq, Ord)

(&*) :: SubstRes -> SubstRes -> SubstRes
Ok &* x = x
x &* Ok = x
NotCorrectSubst &* NotEqual = NotEqual
NotEqual &* NotCorrectSubst = NotEqual
x &* y = x

(-&) :: Bool -> SubstRes -> SubstRes
False -& x = NotEqual
_ -& x = x

(&-) :: SubstRes -> Bool -> SubstRes
x &- y = y -& x

(|-) :: SubstRes -> Bool -> SubstRes
_ |- True = Ok
x |- _ = x

checkAxiom :: PredMap -> Expression -> Expression -> (Bool, PredMap)
checkAxiom myMap expr (Pred x) = if found == Nothing
                                    then (True, M.insert x expr myMap)
                                else ((fromJust found) == expr, myMap)
                                where 
                                    found = (M.lookup x myMap) 

checkAxiom myMap (BinaryExpression leftE rightE operE) (BinaryExpression leftA rightA operA) = 
                                ((operA == operE) && (leftB) && (rightB), rightM)
                                where 
                                    (leftB, leftM) = (checkAxiom myMap leftE leftA)
                                    (rightB, rightM) = (checkAxiom leftM rightE rightA)

checkAxiom myMap (UnaryExpression rightE operE) (UnaryExpression rightA operA) = 
                                ((operA == operE && (boo)), map)
                                where
                                    (boo, map) = (checkAxiom myMap rightE rightA)

checkAxiom myMap _ _ = (False, myMap)

isSubst:: Term -> Maybe Term -> S.Set Term -> S.Set Term -> Expression -> Expression -> (SubstRes, S.Set Term, Maybe Term)
isSubst x theta locked inTheta 
					(BinaryExpression leftE rightE operE) (BinaryExpression leftA rightA operA) = 
						((operA == operE) -& (leftB) &* (rightB), rInTheta, rTerm)
						where 
							(leftB, lInTheta, lTerm) = isSubst x theta locked inTheta leftE leftA
							(rightB, rInTheta, rTerm) = isSubst x lTerm locked lInTheta rightE rightA

isSubst x theta locked inTheta
					(UnaryExpression rightE operE) (UnaryExpression rightA operA) = 
                                (((operA == operE) -& boo), rInTheta, rTerm)
                                where
                                    (boo, rInTheta, rTerm) = (isSubst x theta locked inTheta rightE rightA)

isSubst x theta locked inTheta
					(Pred (Symbol leftN leftA)) (Pred (Symbol rightN rightA)) = 
						((leftN == rightN) -& ch, rInTheta, rTheta)
						where 
							(ch, rTheta, rInTheta) = checkArgsForSubst x theta locked inTheta leftA rightA 

isSubst x theta locked inTheta
					(Pred (Eq leftLT leftRT)) (Pred (Eq rightLT rightRT)) = 
						isSubst x theta locked inTheta (Pred (Symbol "`" [leftLT, leftRT])) (Pred (Symbol "`" [rightLT, rightRT]))

isSubst x theta locked inTheta
					(Quant leftQ leftV leftE) (Quant rightQ rightV rightE) = 
						let 
							newSet = S.insert leftV locked
							(a, c, d) = isSubst x theta newSet inTheta leftE rightE
						in ((a &- (leftQ == rightQ) &- (leftV == rightV)), c, d)

isSubst _ _ _ _ _ _ = (NotEqual, S.empty, Nothing)

checkArgsForSubst :: Term -> Maybe Term -> S.Set Term -> S.Set Term -> [Term] -> [Term] -> (SubstRes, Maybe Term, S.Set Term)
checkArgsForSubst x theta locked inTheta a b = foldl (\(q, th, inTh) (a1, a2) -> 
									let (a, b, c) = checkTermsForSubst x th a1 a2 locked inTh
									in (q &* a, b, c)) (Ok, theta, inTheta) (zip a b)


checkTermsForSubst :: Term -> Maybe Term -> Term -> Term -> S.Set Term -> S.Set Term -> (SubstRes, Maybe Term, S.Set Term)
checkTermsForSubst x theta (BinaryTerm lA rA oA) (BinaryTerm lB rB oB) locked inTheta = checkTermsForSubst x theta (Application (show oA) [lA, rA]) (Application (show oB) [lB, rB]) locked inTheta
checkTermsForSubst x theta (Application nL argL) (Application nR argR) locked inTheta = 
																let (a, b, c) = foldl (\(sres, thet, inth) (term1, term2) -> 
																	let (a, b, c) = checkTermsForSubst x thet term1 term2 locked inth in
																	(a &* sres, b, c)) (Ok, theta, inTheta) (zip argL argR) 
																in (a &- (nR == nL), b, c)
checkTermsForSubst x theta (Inc aL) (Inc aR) locked inTheta = checkTermsForSubst x theta (Application "`" [aL]) (Application "`" [aR]) locked inTheta
checkTermsForSubst x theta (Z) (Z) locked inTheta = (Ok, theta, inTheta)
checkTermsForSubst x theta v@(Variable n) l locked inTheta = 
										if v == x && S.notMember v locked then
											let 
												isAvailable inT = if (S.size (S.intersection inT locked) == 0) then Ok else NotCorrectSubst
												set = makeSet l in
											if theta == Nothing then
												(Ok &* isAvailable set, Just l, set)
											else
												((l == (fromJust theta)) -& (isAvailable inTheta), Just l, inTheta)
										else
											((v == l) -& Ok, theta, inTheta)
checkTermsForSubst _ t _ _ _ tt = (NotEqual, t, tt)

checkForSubst :: Term -> Expression -> Expression -> (SubstRes, Maybe Term)
checkForSubst x a b = let (c, _, e) = isSubst x Nothing S.empty S.empty a b in (c, e)

makeSet :: Term -> S.Set Term
makeSet (BinaryTerm l r _) = S.union (makeSet l) (makeSet r)
makeSet (Application _ a) = foldl (\b c -> S.union b (makeSet c)) S.empty a
makeSet b@(Variable _) = S.singleton b
makeSet (Inc a) = makeSet a
makeSet _ = S.empty

check11 :: Expression -> (SubstRes, Maybe Term)
check11 (BinaryExpression (Quant All var expr1) expr2 Impl) = checkForSubst var expr1 expr2
check11 _ = (NotEqual, Nothing)

check12 :: Expression -> (SubstRes, Maybe Term)
check12 (BinaryExpression expr1 (Quant Exists var expr2) Impl) = checkForSubst var expr2 expr1
check12 _ = (NotEqual, Nothing)

checkInd :: Expression -> Maybe Int
checkInd (BinaryExpression (BinaryExpression expr1 (Quant All x (BinaryExpression expr2 expr3 Impl)) Conj) expr4 Impl) = 
				let 
					(q1, theta1) = checkForSubst x expr4 expr1
					(q2, theta2) = checkForSubst x expr4 expr3 
				in if ((q1 &* q2 &- (theta1 == (Just Z)) &- (theta2 == (Just (Inc x))) &- (expr2 == expr4)) == Ok) then Just 13
					else Nothing

checkInd _ = Nothing

checkAxioms :: Expression -> Maybe Int
checkAxioms expr = foldl1 addMaybe [findIndex (\axiom -> fst $ checkAxiom M.empty expr axiom) axioms,
									findIndex (==expr) axiomsArithm, checkInd expr]

checkMP :: [(Expression, Int)] -> Expression -> M.Map Expression Int -> (Maybe Expression, Maybe Expression)
checkMP [] _ _ = (Nothing, Nothing)
checkMP proof expr map =  ((left.fst) <$> fi, (fst) <$> fi)-- proof - forall fi : fi->expr
                        where 
                            fi = find f proof
                            f ((BinaryExpression leftE rightE Impl), _) = (M.member leftE map) && (rightE == expr) -- maybe last condition is not necessary
                            f _ = False

isLockedExpr :: Term -> Expression -> S.Set Term -> Bool
isLockedExpr x (BinaryExpression a b _) s = isLockedExpr x a s && isLockedExpr x b s
isLockedExpr x (UnaryExpression a _) s = isLockedExpr x a s
isLockedExpr x (Quant _ y expr) s = isLockedExpr x expr (S.insert y s)
isLockedExpr x (Pred (Symbol _ ar)) s = foldl (\y z -> isLockedTerm x z s && y) True ar
isLockedExpr x (Pred (Eq a b)) s = isLockedExpr x (Pred (Symbol "`" [a, b])) s

isLockedTerm :: Term -> Term -> S.Set Term -> Bool
isLockedTerm x y s = let un = makeSet y in S.notMember x un || S.member x s

checkRules :: Expression -> M.Map Expression Int -> SubstRes
checkRules (BinaryExpression a (Quant All x b) Impl) map = M.member (BinaryExpression a b Impl) map -& if isLockedExpr x a S.empty then Ok else NotCorrectSubst
checkRules (BinaryExpression (Quant Exists x b) a Impl) map = M.member (BinaryExpression b a Impl) map -& if isLockedExpr x a S.empty then Ok else NotCorrectSubst
checkRules _ _ = NotEqual

getAxError :: Expression -> Term -> Error
getAxError (BinaryExpression (Quant All x expr1) _ Impl) theta = NotFreeForSubst theta expr1 x
getAxError (BinaryExpression _ (Quant Exists x expr1) Impl) theta = NotFreeForSubst theta expr1 x
getAxError _ _ = NoProof -- Unreachable

getConcError :: Expression -> Error
getConcError (BinaryExpression expr1 (Quant All x expr2) Impl) = FreeForSubst expr1 x
getConcError (BinaryExpression (Quant Exists x expr1) expr2 Impl) = FreeForSubst expr2 x
getConcError _ = NoProof -- Unreachable

checkForFreeInAss :: Expression -> Maybe Expression -> Bool
checkForFreeInAss (BinaryExpression _ (Quant All x _) Impl) (Just a) = not $ isLockedExpr x a S.empty
checkForFreeInAss (BinaryExpression (Quant Exists x _) _ Impl) (Just a) = not $ isLockedExpr x a S.empty
checkForFreeInAss _ _ = False

getConcFreeErr :: Expression -> Maybe Expression -> Error
getConcFreeErr (BinaryExpression _ (Quant All x _) Impl) (Just a) = FreeForSubstInAss a x
getConcFreeErr (BinaryExpression (Quant Exists x _) _ Impl) (Just a) = FreeForSubstInAss a x
getConcFreeErr _ _ = NoProof

temp = Pred (Symbol "`" [])

getConclusion :: Expression -> Annotation
getConclusion a@(BinaryExpression f (Quant All x s) Impl) = Conclusion (BinaryExpression f s Impl) temp ForAll
getConclusion a@(BinaryExpression (Quant Exists x f) s Impl) = Conclusion (BinaryExpression f s Impl) temp ForOne

splitByComma :: String -> [String]
splitByComma s = let (_, arr, last) = foldl (\(p, arr, currStr) ch -> case ch of 
															'(' -> (p + 1, arr, ch:currStr)
															',' -> if p == 0 then (p, (reverse currStr):arr, "")
																	else (p, arr, ch:currStr)
															')' -> (p - 1, arr, ch:currStr)
															_ -> (p, arr, ch:currStr)) (0, [], "") s in filter (/= "") (reverse ((reverse last):arr))


parseProof :: String -> [String] -> ([(Expression, Annotation)], Maybe ErrorWithNum, Maybe (Expression, Int), String)
parseProof decl strproof = let 
        [assumptions, strGoal] = let (a, _) = foldl (\(q, prev) ch -> 
        											(q || prev == '|' && ch == '-', ch)
        											) (False, '`') decl 
        							in if a then splitOn "|-" decl else ["", ""]
        strAssump = splitByComma assumptions
        assumpLength = length assump
        assump = map parse strAssump
        proof = map parse strproof
        alphaWithNum = if assumptions /= [] then Just $ (last assump, length assump) else Nothing
        alpha = fst <$> alphaWithNum
        (annotations, error, _, _, _, _) = foldl (\(proofs, err, map, currproofs, implMap, currLength) line -> let 
                axiomN = checkAxioms line
                mp = checkMP (MM.lookup line implMap) line map
                rules = checkRules line map
                (twelfth, theta12) = check12 line
                (eleventh, theta11) = check11 line
                assN = findIndex (== line) assump
                annot = if axiomN /= Nothing || twelfth == Ok || eleventh == Ok then if axiomN /= Nothing then (Axiom (fromJust axiomN)) else
                												if (twelfth == Ok) then Axiom 12 else Axiom 11
                		else if (fst mp) /= Nothing then let 
								i_th = fromJust $ fst mp
								j_th = fromJust $ snd mp 
							in (Conclusion i_th j_th MP) 
                		else if (rules == Ok && (not $ checkForFreeInAss line alpha)) then getConclusion line
                		else if assN /= Nothing then (Assumption (fromJust assN))
                		else NotProven
                er = if twelfth == NotCorrectSubst then Just (Err (getAxError line (fromJust theta12)) len)
                		else if eleventh == NotCorrectSubst then Just (Err (getAxError line (fromJust theta11)) len)
                		else if rules == NotCorrectSubst then Just (Err (getConcError line) len) 
                		else if rules == Ok && checkForFreeInAss line alpha then Just (Err (getConcFreeErr line alpha) len)
                		else if annot == NotProven then Just (Err NoProof len)
                		else Nothing
                len = currLength + 1
                newImplMap expr@(BinaryExpression left right Impl) mmap = MM.insert right (expr, len) mmap
                newImplMap _ map = map
                newErr = if err /= Nothing then err else er
                newProof = if newErr /= Nothing then proofs else (annot):proofs
                in (newProof, newErr, M.insert line len map, line:currproofs, (newImplMap line implMap), len)) ([], Nothing, M.empty, [], MM.empty, 0) proof
        in (zip proof (reverse annotations), error, alphaWithNum, decl)

parseP :: [String] -> ([(Expression, Annotation)], Maybe ErrorWithNum, Maybe (Expression, Int), String)
parseP s = parseProof (head s) (tail s)
