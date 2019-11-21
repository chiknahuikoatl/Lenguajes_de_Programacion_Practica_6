module BAE.Semantic where

import Data.List


data Expr = V Identifier | I Int | B Bool
            | Add Expr Expr | Mul Expr Expr
            | Succ Expr | Pred Expr | Not Expr | And Expr Expr
            | Or Expr Expr | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
            | If Expr Expr Expr | Let Identifier Expr Expr  deriving (Eq)
            | Fn Identifier Expr | App Expr Expr

type Identifier = Int

infix :->

data Type = T Identifier | Integer | Boolean | Type :-> Type

type Substitution = [(Identifier, Type)]

vars :: Type -> [Identifier]
vars (T n) = [n]
vars Integer = []
vars Boolean = []
vars ((T n) :-> t) = if (elem n m)
                        then m
                        else (n:m)  where m = (vars t)
vars (_ :-> t) = (vars t)

subst :: Type -> Substitution -> Type
subst (t1 :-> t2) s = ((substAux t1 s) :-> (subst t2 s))
subst t s = (substAux t s)

substAux :: Type -> Substitution -> Type
substAux t [] = t
substAux Integer _ = Integer
substAux Boolean _ = Boolean
substAux (T n) ((m, s1):s) = if (n == m)
                                    then s1
                                    else (substAux (T n) s)
substAux t (_:s) = (substAux t s)

comp :: Substitution -> Substitution -> Substitution
comp [] s = s
comp (x:xs) ys = ([x] ++ (comp xs ys))

simpl :: Substitution -> Substitution
simpl [] = []
simpl ((n,t):s) = ((simplAux n t) ++ (simpl s))

simplAux :: Identifier -> Type -> Substitution
simplAux n (T m) = if (m == n) then [] else [(n, (T m))]
simpleAux n t = [(n,t)]
