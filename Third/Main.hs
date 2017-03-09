import Predicate.Parser
import Predicate.Axioms
import Predicate.Builder
import qualified Data.String.Utils as Utils

zzz = replace' [(Pred (Eq Z Z))] "0->0->0"
abc = ['a', 'b', 'c']
temp = Variable "`"
equiv = parse "a=a"

replaceQuantor :: Expression -> Term -> Expression
replaceQuantor (Quant _ (Variable n) e) r = parse (Utils.replace n ("(" ++ (show r) ++ ")") (show e))

createAxiom' :: Expression -> [Term] -> [Expression]
createAxiom' ax terms = ax : (map (replace' [ax, zzz]) (["0->1->0", "1->0"] ++ (fst $ foldr (\term (ans, curr) -> let a = '@':term:curr in (ans ++ [("1->" ++ a)], a)) ([], "(0)") abc)))
										++ foldl (\ans term -> let
			 											las = last ans 
			 											a = replaceQuantor las term 
			 							in (ans ++ [(replace' [las, a] "0->1"), a])) [replace' [ax, zzz] "@a@b@c(0)"] terms  

createAxiom :: Expression -> [Term] -> [Expression]
createAxiom ax [t] = createAxiom ax [t, temp]
createAxiom ax [t1, t2] = createAxiom ax [t1, t2, temp]
createAxiom ax t = createAxiom' ax t

createAxiomWN :: Int -> [Term] -> [Expression]
createAxiomWN 7 t = createAxiom equiv t
createAxiomWN num t = createAxiom (axiomsArithm !! num) t

termFromNum :: Int -> Term
termFromNum 0 = Z
termFromNum x = Inc $ termFromNum (x - 1)

add :: Term -> Term -> Term
add a b = BinaryTerm a b Add

less :: Int -> Int -> [Expression]
less a b = 
	let 
		x = termFromNum a
		y = termFromNum b 
		l = replace' [x, termFromNum (b - a), y] "0+1=2"
		las = replace' [l, last] "0->1"
		last = replace' [x, y] "?a(0+a)=1"
  	in (createAxiomWN 4 [x]) ++ (foldr (\dif ans -> 
		let 
			difTerm = termFromNum dif 
			sum = termFromNum $ dif + a
			e = replace' [x, difTerm, sum] "(0+1)'=2'"
			f = replace' [x, difTerm, sum] "0+1'=2'"
			c = add x (Inc difTerm)
			d = Inc (add x difTerm)
		 in (concat [createAxiomWN 0 [add x difTerm, termFromNum (dif + a)], [e], 
							  createAxiomWN 3 [x, difTerm], 
							  createAxiomWN 7 [c], createAxiomWN 1 [c, d, c], map (replace' [c, d]) ["(0=0)->(1=0)", "1=0"],
							  createAxiomWN 1 [Inc (add x difTerm), add x (Inc difTerm), Inc sum],
							  [replace' [e, f] "0->1"], [f]]) ++ ans) [] [0..(b-a-1)]) ++ [las, last]

rep :: Int -> Int -> String -> String
rep a b str = let f = \x ch str -> Utils.replace ch (take x $ repeat '\'') str in f (a-b-1) "C" (f b "B" str)

more :: Int -> Int -> [String] -> String
more a b arr = concat $ map (\s -> rep a b s ++ "\n") arr

main = do 
	abba <- readFile "abba"
	morgan <- readFile "morgan"
	lem <- readFile "lemma"
	com <- readFile "com"
	lem2 <- readFile "lemma2"
	a <- readLn
	b <- readLn
	writeFile "a.out" (let f = (\str ans-> (show str) ++ "\n" ++ ans) in
					  abba ++ "\n" ++
					  if (a < b) then 
						(foldr f "" (less a b))
					  else
					  	more a b [com, lem, lem2, morgan])

