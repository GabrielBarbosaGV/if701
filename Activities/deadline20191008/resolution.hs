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
  | True
  | False

type Subst = [(String, Prop)]

-- Evaluation of propositions
eval :: Subst -> Prop -> Prop
eval subst (Var string) = substValue subst (Var string)

-- Find value of variable in Subst
substValue :: Subst -> Prop -> Prop
substValue ((storedName, value):vs) (Var name)
  | storedName == name = value
  | otherwise = substValue vs (Var name)
