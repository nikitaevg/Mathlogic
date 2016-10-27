{-# LANGUAGE DeriveGeneric #-}

import Data.Char
import System.IO
import Data.List
import Data.List.Split
import Control.Monad
import Data.Maybe
import GHC.Generics
import qualified Data.HashMap as M
import qualified Data.MultiMap as MM
import Data.Hashable

data Expression = BinaryExpression {left :: Expression,
                                    right :: Expression,
                                    operator :: Operator} |
                  UnaryExpression {right :: Expression,
                                   operator :: Operator} |
                  Operand {operand :: String} deriving (Show, Eq, Ord, Generic)

data Operator = Impl | Disj | Conj | Neg | Bracket deriving (Eq, Show, Ord, Generic)

instance Hashable Expression where 
    hashWithSalt s (BinaryExpression left right oper) = 239 * (hashWithSalt s left) + 7193 * (hashWithSalt s right) + 2971 * (hashWithSalt s oper) + s
    hashWithSalt s (UnaryExpression right oper) = 1319 * (hashWithSalt s right) + 1439 * (hashWithSalt s oper) + s
    hashWithSalt s (Operand op) = hashWithSalt s op + s

instance Hashable Operator where
    hashWithSalt s Impl = 1303 + s
    hashWithSalt s Disj = 1667 + s
    hashWithSalt s Conj = 1823 + s
    hashWithSalt s Neg = 2063 + s

priority :: Operator -> Int
priority x
    | x == Impl = 1
    | x == Disj = 2
    | x == Conj = 3
    | x == Neg = 4
    | otherwise = 100

isRightAssos :: Operator -> Bool
isRightAssos (Impl) = True
isRightAssos (Neg) = True
isRightAssos _ = False

isOperand :: String -> Bool
isOperand = any isAlpha

divideByTokens :: String -> [String]
divideByTokens "" = []
divideByTokens str@(x:xs)
                        | operatorByString [x] /= Nothing = [x] : (divideByTokens xs)
                        | otherwise = let 
                                        f = if isSmth x then not else id
                                        (a, b) = break (\x -> ((f $ isSmth x) || (x == ')') || (x == '(') || (x == '!'))) str 
                                      in a:(divideByTokens b)
                                      where isSmth ch = isAlpha ch || isDigit ch

operatorByString :: String -> (Maybe Operator)
operatorByString st
                   | st == "|" = Just Disj
                   | st == "&" = Just Conj
                   | st == "->" = Just Impl
                   | st == "!" = Just Neg
                   | st == ")" || st == "(" = Just Bracket
                   | otherwise = Nothing


firstOPN :: [String] -> ([String], [String])
firstOPN = let
                operator = fromJust.operatorByString 
                getPri = priority.operator
                getRight = isRightAssos.operator
                shouldPop a b = ((getPri a <= getPri b) && (getRight a)) || ((getPri a < getPri b) && (not $ getRight a)) || (a == "(")
              in foldl (\(ans, st) ch -> 
                if (isOperand ch)
                       then (ch:ans, st)
                   else if (ch == "(")
                       then (ans, ch:st)
                   else if (ch == ")")
                       then let (x, y) = break (== "(") st in ((reverse x) ++ ans, tail y)
                   else let (a, b) = break (\op -> shouldPop op ch) st 
                          in ((reverse a) ++ ans, ch:b)) 
                ([], [])

secondOPN :: ([String], [String]) -> [String]
secondOPN (ans, st) = (reverse ans) ++ st

opn :: String -> [String]
opn = secondOPN . firstOPN . divideByTokens

opnToExp :: [String] -> Expression
opnToExp str = head $ foldl (\st ch -> 
                            if isOperand ch
                                then (Operand ch):st
                            else if ch == "!"
                                then (UnaryExpression (head st) Neg):(drop 1 st)
                            else
                                (BinaryExpression (st !! 1) (head st) (fromJust (operatorByString ch))):(drop 2 st)
                            ) [] str

makeAnExp :: String -> Expression
makeAnExp = opnToExp . opn

checkAxiom :: M.Map String Expression -> Expression -> Expression -> (Bool, M.Map String Expression)
checkAxiom myMap expr (Operand str) = if found == Nothing
                                    then (True, M.insert str expr myMap)
                                else ((fromJust found) == expr, myMap)
                                where 
                                    found = (M.lookup str myMap) 

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

checkAxioms :: [Expression] -> Expression -> Maybe Int
checkAxioms axioms expr = findIndex (\axiom -> fst $ checkAxiom M.empty expr axiom) axioms

checkMP :: [(Expression, Int)] -> Expression -> M.Map Expression Int -> (Maybe Int, Maybe Int)
checkMP [] _ _ = (Nothing, Nothing)
checkMP proof expr map = (globalIndex, join $ (\t -> M.lookup (left $ fst $ proof !! t) map) <$> localIndex)
                        where 
                            globalIndex = (\t -> snd $ proof !! t) <$> localIndex
                            localIndex = findIndex f proof
                            f ((BinaryExpression left right Impl), _) = (M.member left map) && (right == expr)
                            f _ = False

axioms = map f 
         ["f->x->f",
          "(f->p)->(f->p->r)->(f->r)",
          "f->(p->(f&p))",
          "f&p->f",
          "f&p->p",
          "f->f|p",
          "p->f|p",
          "(f->r)->(p->r)->((f|p)->r)",
          "(f->p)->(f->!p)->!f",
          "!!f->f"]
          where f = makeAnExp

parse :: String -> [String] -> String
parse decl strproof = let 
        [assumptions, strGoal] = splitOn "|-" decl
        assump = map makeAnExp $ splitOn "," assumptions
        proof = map makeAnExp strproof
        (annotations, _, _, _) = foldl (\(proofs, map, currproofs, implMap) line -> let 
                axiomN = checkAxioms axioms line
                mp = checkMP (MM.lookup line implMap) line map
                assN = findIndex (== line) assump
                annot = if axiomN /= Nothing
                            then (\x -> "Сх. акс. " ++ show (x + 1)) <$> axiomN
                         else if (fst mp) /= Nothing
                             then ((\x y z n -> x ++ (show $ y) ++ ", " ++ (show $ z)) <$> Just "M.P. " <*> (snd mp) <*> (fst mp) <*> Just (length currproofs))
                         else if assN /= Nothing
                             then (\x -> "Предп. " ++ show (x + 1)) <$> assN
                         else Just "Не доказано"
                len = length proofs + 1
                newImplMap expr@(BinaryExpression left right Impl) mmap = MM.insert right (expr, len) mmap
                newImplMap _ map = map
                in ((fromJust annot):proofs, M.insert line len map, line:currproofs, (newImplMap line implMap))) ([], M.empty, [], MM.empty) proof
        in foldl1 (\ans s -> s ++ "\n" ++ ans) $ reverse $ zipWith3 (\num proof annot -> "(" ++ show num ++ ") " ++ proof ++ " (" ++ annot ++ ")") [1..] strproof $ reverse annotations


main = do
    contents <- readFile "a.in"
    writeFile "a.out" (let lines = filter (/="") $ splitOn "\n" (filter (/=' ') contents) in parse (head lines) (tail lines))










