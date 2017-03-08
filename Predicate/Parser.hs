module Predicate.Parser
(Expression(..),
  Operator(..),
  Predicate(..),
  Quantor(..),
  Term(..),
  TOperator(..),
  parse) where

import Data.Char
import Data.Maybe


data Expression = BinaryExpression {left :: Expression,
                                    right :: Expression,
                                    operator :: Operator} 
                  | UnaryExpression {expr :: Expression,
                             operator :: Operator} 
                  | Quant {quant :: Quantor,
                           var :: Term,
                           expr :: Expression}
                  | Pred {pred :: Predicate} deriving (Eq, Ord)

addBrackets :: String -> String
addBrackets s = "(" ++ s ++ ")"

instance Show Expression where
  show (BinaryExpression l r o) = addBrackets $ show l ++ show o ++ show r
  show (UnaryExpression e o) = show o ++ show e
  show (Quant q v e) = show q ++ show v ++ show e
  show (Pred p) = show p

data Operator = Impl | Disj | Conj | Bracket | Neg | Increase deriving (Eq, Ord)
instance Show Operator where
  show Impl = "->"
  show Disj = "|"
  show Conj = "&"
  show Neg = "!"

data Predicate = Symbol {nameP :: String,
                         args :: [Term]}
                | Eq {leftTerm :: Term,
                      rightTerm :: Term} deriving (Eq, Ord)

tempFunc arr = if (length arr > 0) then 
                let (a, _) = foldr (\ch (s, comma) -> (((show ch) ++ (if comma then "," else "") ++ s), True)) ("", False) arr
                in addBrackets a
               else ""

instance Show Predicate where
  show (Symbol n a) = n ++ (tempFunc a)
  show (Eq l r) = show l ++ "=" ++ show r

data Quantor = Exists | All deriving (Eq, Ord)
instance Show Quantor where
  show Exists = "?"
  show All = "@"
data Term = BinaryTerm {leftT :: Term,
                        rightT :: Term,
                        operatorT :: TOperator}
            | Application {nameT :: String,
                           argsT :: [Term]}
            | Variable {nameT :: String}
            | Z
            | Inc {exprT :: Term} deriving (Eq, Ord)

instance Show Term where
  show (BinaryTerm l r t) = addBrackets $ show l ++ show t ++ show r
  show (Application n a) = n ++ (tempFunc a)
  show (Variable n) = n
  show (Z) = "0"
  show (Inc e) = show e ++ "\'"

data TOperator = Add | Mul deriving (Eq, Ord)
instance Show TOperator where
  show Add = "+"
  show Mul = "*"

operatorByString :: String -> Maybe Operator
operatorByString st
                   | st == "|" = Just Disj
                   | st == "&" = Just Conj
                   | st == "->" = Just Impl
                   | st == "!" = Just Neg
                   | st == ")" || st == "(" = Just Bracket
                   | st == "'" = Just Increase
                   | otherwise = Nothing

quantorByString :: String -> Maybe Quantor
quantorByString st
                  | st == "@" = Just All
                  | st == "?" = Just Exists
                  | otherwise = Nothing

tOperatorByString :: String -> Maybe TOperator
tOperatorByString st 
                    | st == "+" = Just Add
                    | st == "*" = Just Mul
                    | otherwise = Nothing

isOperator :: String -> Bool
isOperator x = operatorByString x /= Nothing || quantorByString x /= Nothing || tOperatorByString x /= Nothing

isCharOperator :: Char -> Bool
isCharOperator x = isOperator [x]

divideByTokens :: String -> [String]
divideByTokens "" = []
divideByTokens str@(x:xs)
                      | isOperator [x] == True = [x] : (divideByTokens xs)
                      | otherwise = let 
                                        f = if isSmth x then not else id
                                        sameCase y = (not $ isAlpha y) || (not $ isAlpha x) || (isUpper x == isUpper y)
                                        (a, b) = break (\x -> ((f $ isSmth x) || isCharOperator x || not (sameCase x))) str 
                                      in a:(divideByTokens b)
                                      where isSmth ch = isAlpha ch || isDigit ch

divideByTokens' :: String -> [String]
divideByTokens' s = map (filter (/= ' ')) (filter (\x -> x /= " " && x /= "") (divideByTokens s))

myHead :: [String] -> String
myHead [] = ""
myHead s = head s

myTail :: [String] -> [String]
myTail [] = []
myTail s = tail s

parseExpr :: [String] -> (Expression, [String])
parseExpr str = let (eaten, leftFromEaten) = parseDisj str Nothing
                    (right, leftStr) = parseExpr $ myTail leftFromEaten in
                    if myHead leftFromEaten == "->" then (BinaryExpression eaten right Impl, leftStr)
                                    else (eaten, leftFromEaten)

parseDisj :: [String] -> Maybe Expression -> (Expression, [String])
parseDisj str prev = let 
                        (eaten, leftFromEaten) = parseConj str Nothing
                        a = case prev of (Just disj) -> BinaryExpression disj eaten Disj
                                         otherwise -> eaten 
                        (right, leftStr) = parseDisj (myTail leftFromEaten) (Just a) in
                    if myHead leftFromEaten == "|" then (right, leftStr)
                                    else (a, leftFromEaten)

parseConj :: [String] -> Maybe Expression -> (Expression, [String])
parseConj str prev = let 
                        (eaten, leftFromEaten) = parseUnary str 
                        a = case prev of (Just disj) -> BinaryExpression disj eaten Conj
                                         otherwise -> eaten 
                        (right, leftStr) = parseConj (myTail leftFromEaten) (Just a) in
                    if myHead leftFromEaten == "&" then (right, leftStr)
                                    else (a, leftFromEaten)

parseUnary :: [String] -> (Expression, [String])
parseUnary str@(x:left)
                | x == "!" = let (a, b) = parseUnary left in (UnaryExpression a Neg, b)
                | quantorByString x /= Nothing = let (parsed, notParsed) = parseUnary $ myTail left in
                                                (Quant (fromJust $ quantorByString x) (Variable (head left)) parsed, notParsed)
                | x == "(" = 
                  let 
                    (parsed, notParsed) = parseExpr left
                    (a, b) = parsePred str in
                    if (notParsed == [] || (myHead $ notParsed) /= ")") then 
                      (Pred a, b);
                    else
                      (parsed, myTail notParsed)

parseUnary str = let (parsed, left) = parsePred str in (Pred parsed, left)

getArgs :: [String] -> ([Term], [String])
getArgs (")":xs) = ([], xs)
getArgs (",":xs) = let (parsed, left) = parseTerm xs
                       (leftArgs, leftTokens) = getArgs left in
                            (parsed:leftArgs, leftTokens)
getArgs str = getArgs (",":str)


parsePred :: [String] -> (Predicate, [String])
parsePred str@(x:xs) = if isUpper $ head x then 
                                    if myHead xs == "(" then let (args, aft) = getArgs $ tail xs in
                                            (Symbol x args, aft)
                                    else (Symbol x [], xs)
                       else let 
                          (first, left) = parseTerm str
                          (second, lef) = parseTerm $ myTail left in
                                            if myHead left == "=" then 
                                              (Eq first second, lef) 
                                            else 
                                              (Symbol "`" [], ["`"])

parseTerm :: [String] -> (Term, [String])
parseTerm str = let 
                (first, left) = parseAdded str
                (second, finally) = parseTerm $ myTail left in
                    if myHead left == "+" then (BinaryTerm first second Add, finally)
                                       else (first, left)

parseAdded :: [String] -> (Term, [String])
parseAdded str = let 
                  (first, left) = parseMul' str
                  (second, finally) = parseAdded $ myTail left in
                    if myHead left == "*" then (BinaryTerm first second Mul, finally)
                                       else (first, left)

parseMul' :: [String] -> (Term, [String])
parseMul' str = let a@(parsed, left) = parseMul str
                    (strokes, notStrokes) = break (/="'") left in 
                        (foldl (\term _ -> Inc term) parsed strokes, notStrokes)

parseMul :: [String] -> (Term, [String])
parseMul ("0":xs) = (Z, xs)
parseMul ("(":xs) = let (f, s) = parseTerm xs in (f, myTail s)
parseMul (x:xs) = if myHead xs == "(" then 
                                        let (args, left) = getArgs $ tail xs in 
                                                (Application x args, left)
                                    else
                                        if isLower $ head x then (Variable x, xs) else (Variable "`", ["`"])


parse :: String -> Expression
parse = fst.parseExpr.divideByTokens'
