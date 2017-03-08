import Predicate.Builder
import Predicate.Checker
import Data.List.Split
import Predicate.Parser

printA :: (Maybe ([Expression]), Maybe ErrorWithNum) -> String
printA (Nothing, Just err) = show err
printA (Just arr, Nothing) = foldr1 (\str acc -> str ++ "\n" ++ acc) (map show arr)

main = do
	eleventhA <- readFile "11a"
	eleventhB <- readFile "11b"
	twelfth <- readFile "12"
	input <- readFile "a.in"
	let 
		f = filter (/="") . (splitOn "\n") 
		(a, b, c, d) = (parseP $ f input) in
			writeFile "a.out" (printA ((build (a, b, c) ((f eleventhA, f eleventhB), f twelfth))))