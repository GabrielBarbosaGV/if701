-- First Activity

import Data.Char
import Data.List


-- Caesar's Cipher
-- Encoding

-- Converts character in [a-z] to integer in range 0-26
let2int :: Char -> Int
let2int character = ord character - 97


-- Converts integer in range 0-26 to character in [a-z]
int2let :: Int -> Char
int2let integer = chr (integer + 97)


-- Shifts given character by given integer in range [a-z]
shift :: Int -> Char -> Char
shift distance character = int2let (distance + let2int character)


-- Shifts all character of string by given distance
encode :: Int -> String -> String
encode distance string = map (shift distance) string

-- Decoding
percent :: Int -> Int -> Float
percent part whole = 100 * numPart / numWhole
  where numPart = fromIntegral part
        numWhole = fromIntegral whole

-- Returns list of frequencies of characters in given string
-- in same order as they appeard
freqs :: String -> [Float]
freqs string =
  let uniqueString = getCharacters string
      occurrenceNumberForChar =
        map (howManyOfCharacterInString string) uniqueString
      percentages =
        map (\x -> percent x (length string)) occurrenceNumberForChar
      in percentages

-- String with unique characters from given String
getCharacters :: String -> String
getCharacters string = nub string

-- Return number of occurrences of given character
-- in string
howManyOfCharacterInString :: String -> Char -> Int
howManyOfCharacterInString string character =
  length (filter (==character) string)

-- Compares observed with expected recurrence frequency
chisqr :: [Float] -> [Float] -> Float
chisqr observed expected =
  sum (map (\(x,y) -> chiUnit x y) (zip observed expected))

-- Perform chi-squared operation for pair of values
chiUnit :: Float -> Float -> Float
chiUnit observed expected =
  (observed - expected)^2 / expected

-- Shift elements of list by given number of positions
rotate :: Int -> [a] -> [a]
rotate amount list = lastPart ++ firstPart
  where amountFromEnd = length list - amount
        firstPart = take amountFromEnd list
        lastPart = drop amountFromEnd list

{-
crack :: String -> String
crack string =
  let len = length string
      chiSquareds = 
-}


-- Tautology verifier

-- Algebraic data type

data Prop = Imply Prop Prop
  | BiImply Prop Prop
  | And Prop Prop
  | Or Prop Prop
  | Negation Prop
  | Var String
  | T
  | F deriving (Show, Eq)

type Subst = [(String, Prop)]

-- Evaluation of propositions
eval :: Subst -> Prop -> Prop
eval _ T = T
eval _ F = F
eval _ (Imply T F) = F
eval _ (Imply F _) = T
eval _ (Imply T _) = T
eval _ (BiImply T T) = T
eval _ (BiImply F F) = T
eval _ (BiImply _ F) = F
eval _ (BiImply F _) = F
eval _ (And T T) = T
eval _ (And F _) = F
eval _ (And _ F) = F
eval _ (Or F F) = F
eval _ (Or T _) = T
eval _ (Or _ T) = T
eval _ (Negation T) = F
eval _ (Negation F) = T
eval subst (Imply first second) =
  eval subst (Imply (eval subst first) (eval subst second))
eval subst (BiImply first second) =
  eval subst (BiImply (eval subst first) (eval subst second))
eval subst (And first second) =
  eval subst (And (eval subst first) (eval subst second))
eval subst (Or first second) =
  eval subst (Or (eval subst first) (eval subst second))
eval subst (Negation prop) =
  eval subst (Negation (eval subst prop))
eval subst (Var string) =
  substValue subst (Var string)

-- Find value of variable in Subst
substValue :: Subst -> Prop -> Prop
substValue ((storedName, value):vs) (Var name)
  | storedName == name = value
  | otherwise = substValue vs (Var name)

vars :: Prop -> [String]
vars (Var string) = [string]
vars (Imply first second) = (vars first) ++ (vars second)
vars (BiImply first second) = (vars first) ++ (vars second)
vars (And first second) = (vars first) ++ (vars second)
vars (Or first second) = (vars first) ++ (vars second)
vars (Negation prop) = vars prop
vars _ = []

bools :: Int -> [[Prop]]
bools 0 = [[]]
bools n =
  [T:list | list <- bools (n - 1)]
  ++
  [F:list | list <- bools (n - 1)]

substs :: Prop -> [Subst]
substs prop = map (zip (nub varNames)) (bools (length varNames))
  where varNames = vars prop

isTaut :: Prop -> Bool
isTaut prop =
  let substitutions = substs prop
      evaluations = map (\s -> eval s prop) substitutions
      allTrue = (not (elem F evaluations))
      in allTrue


-- Newton's Method
-- Square root
minimalDistance :: Double
minimalDistance = 0.00001

sqroot :: Double -> Double
sqroot value = newtonSqroot value 1 ((1 + 1 / value) / 2)

newtonSqroot :: Double -> Double -> Double -> Double
newtonSqroot value previous current =
  if ((abs (current - previous)) < minimalDistance)
  then current
  else (newtonSqroot value current ((current + value / current) / 2))


-- Set data structure

-- Binary search tree
data Tree a = Leaf a | Node a (Tree a) (Tree a) | Nil

insertInTree :: (Ord a) => Tree a -> a -> Tree a
insertInTree Nil toInsert = (Leaf toInsert)
insertInTree (Leaf value) toInsert
  | toInsert <= value = (Node value (Leaf value) Nil)
  | otherwise = (Node value Nil (Leaf value))
insertInTree (Node value left right) toInsert
  | toInsert <= value = (Node value (insertInTree left toInsert) right)
  | otherwise = (Node value left (insertInTree right toInsert))

mergeTrees :: (Ord a) => Tree a -> Tree a -> Tree a
mergeTrees Nil Nil = Nil
mergeTrees Nil right = right
mergeTrees left Nil = left
mergeTrees (Leaf first) (Leaf second)
  | first <= second = (Node second (Leaf first) Nil)
  | otherwise = (Node first (Leaf second) Nil)
mergeTrees (Leaf first) (Node second left right)
  | first <= second = (Node second (mergeTrees (Leaf first) left) right)
  | otherwise = (Node second left (mergeTrees (Leaf first) right))
mergeTrees node@(Node first left right) leaf@(Leaf second) =
  mergeTrees leaf node
mergeTrees
  first@(Node firstValue firstLeft firstRight)
  second@(Node secondValue secondLeft secondRight)
  | firstValue <= secondValue = (Node secondValue (mergeTrees first secondLeft) secondRight)
  | otherwise = (Node secondValue secondLeft (mergeTrees first secondRight))

removeFromTree :: (Ord a) => Tree a -> a -> Tree a
removeFromTree Nil _ = Nil
removeFromTree (Leaf value) toRemove
  | value == toRemove = Nil
  | otherwise = (Leaf value)
removeFromTree (Node value left right) toRemove
  | value == toRemove = (mergeTrees left right)
  | value < toRemove = (Node value left (removeFromTree right toRemove))
  | value > toRemove = (Node value (removeFromTree left toRemove) right)

isInTree :: (Ord a) => Tree a -> a -> Bool
isInTree Nil _ = False
isInTree (Leaf value) toVerify = value == toVerify
isInTree (Node value left right) toVerify
  | value == toVerify = True
  | value <= toVerify = isInTree right toVerify
  | otherwise = isInTree left toVerify
