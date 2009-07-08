-- Deriving the Symmetric conjunction

module Symm where

type VarName = String
data Val =  V VarName | C String [Val]

newtype Subst = Subst [(VarName,Val)]

data Stream = Fail | One Subst | Choice Subst Susp
            | Inc Susp		-- incomplete answer
type Goal = Subst -> Stream
type Susp = [Cont]  -- non-empty list of continuations
type Cont = (Subst, Goal)

-- Disjunction
mplus :: Goal -> Goal -> Goal
mplus g1 g2 = \s -> mplus' (g1 s) [(s,g2)] -- Try g1 first, suspend  g2

mplus' :: Stream -> Susp -> Stream
mplus' Fail k2 = Inc k2
mplus' (One s1) k2 = Choice s1 k2
mplus' (Choice s1 k1) k2 = Choice s1 (merge k2 k1) -- interleaving
mplus' (Inc k1) ((s2,g2):k2) = mplus'' (g2 s2) (merge k1 k2) -- now try g2

mplus'' :: Stream -> Susp -> Stream
mplus'' Fail k1 = Inc k1
mplus'' (One s2) k1 = Choice s2 k1
mplus'' (Choice s2 k2) k1 = Choice s2 (merge k1 k2) -- interleaving
mplus'' (Inc k2) k1 = Inc (merge k1 k2)

-- Merge two suspensions
merge :: Susp -> Susp -> Susp
merge [k1] k2 = k1:k2
merge k1 [] = k1
merge (k1:k1r) (k2:k2r) = k1:k2:merge k1r k2r

-- Conjunction
conj :: Goal -> Goal -> Goal
conj g1 g2 = \s -> bind (g1 s) g2	-- First run g1, and then g2

bind :: Stream -> Goal -> Stream
bind Fail g2 = Fail
bind (One s1) g2 = Inc [(s1,g2)]	-- Suspend running g2, let others run
bind (Choice s k1) g2 = mplus' (g2 s) (bind' k1 g2)
bind (Inc k1) g2 = Inc (bind' k1 g2)

{-
-- For regular, asymmetric conjunction, we use this:
bind' :: Susp -> Goal -> Susp
bind' k1 g2 = map (\ (s,g) -> (s,conj g g2)) k1
-}

-- To get the symmetric conjunction, we make one change:
bind' :: Susp -> Goal -> Susp
bind' k1 g2 = map (\ (s,g) -> (s,conj g2 g)) k1

