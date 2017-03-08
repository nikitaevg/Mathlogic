module Predicate.Builder
(
	build
)
where
import Predicate.Checker
import Predicate.Parser
import Data.Char

type Files = (([String], [String]), [String])

replace :: [Expression] -> String -> String
replace arr (x:xs) = if isDigit x then ("(" ++ show (arr !! (digitToInt x)) ++ ")") ++ (replace arr xs)
					 else x:(replace arr xs)
replace arr "" = ""

replace' :: [Expression] -> String -> Expression
replace' a s = parse $ replace a s

rebuild :: (Expression, Annotation) -> (Expression, Int) -> Files -> [Expression]
rebuild (line, (Axiom _)) (alpha, _) _ = let rep = replace' [alpha, line] in 
				line:map rep ["1 -> (0 -> 1)", "0 -> 1"]
rebuild (line, (Assumption numAs)) alphaWN@(alpha, numAl) t = let rep = replace' [alpha, line] in 
							if numAl == (numAs + 1) then
										(map rep ["0->(0->0)", "(0->(0->0)) -> (0->((0->0)->0)) -> (0->0)",
											"(0->((0->0)->0)) -> (0->0)", "(0->((0->0)->0))","0->0"])
							else rebuild (line, (Axiom 0)) alphaWN t
rebuild (line, (Conclusion jth (BinaryExpression _ ith Impl) MP)) (alpha, _) _ = let rep = replace' [alpha, jth, ith] in
							(map rep ["(0->1)->(0->1->2)->(0->2)","(0->1->2)->(0->2)", "0->2"])

rebuild ((BinaryExpression fi' psi' _), (Conclusion (BinaryExpression fi psi Impl) _ ForAll)) (alpha, _) ((one, two), _) = 
	let rep psi = replace' [alpha, fi, psi] in 
			map (rep psi) one ++ [rep psi "0&1->2", rep psi' "0&1->2"] ++ map (rep psi') two ++ [rep psi' "0->1->2"]

rebuild ((BinaryExpression psi' fi' _), (Conclusion (BinaryExpression psi fi Impl) _ ForOne)) (alpha, _) (_, one) = 
	let rep alpha psi = replace' [alpha, psi, fi] 
	in map (rep alpha psi) one ++ [rep alpha psi "1->0->2", rep alpha psi' "1->0->2"] ++
	 map (rep psi' alpha) one ++ [rep alpha psi' "0->1->2"]

build :: ([(Expression, Annotation)], Maybe ErrorWithNum, Maybe (Expression, Int)) -> Files -> (Maybe ([Expression]), Maybe ErrorWithNum) 
build (arr, Nothing, Nothing) _ = (return $ fst $ unzip arr, Nothing)
build (arr, Nothing, (Just alphaWN@(alpha, numberA))) t = (Just $ foldr (\line proofs -> 
							rebuild line alphaWN t ++ proofs) [] arr, Nothing)
build (_, err, _) _ = (Nothing, err)