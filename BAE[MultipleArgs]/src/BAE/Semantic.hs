module BAE.Semantic where

import Data.List
import Data.Char

{-Primero renombramos el tipo de datos	String a Identifier para representar
el conjunto de nombres de variables como cadenas de texto-}
type Identifier = String

{-Sintaxis de expresiones EAB -}
data Expr = V Identifier | I Int | B Bool
            | Add Expr Expr | Mul Expr Expr
            | Succ Expr | Pred Expr
            | Not Expr | And Expr Expr | Or Expr Expr
            | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
            | If Expr Expr Expr
            | Let Identifier Expr Expr
            | Fn Identifier Expr
            | App Expr Expr deriving (Eq)

{-Crea una instancia de la class Show que muestra las expresiones
en sintaxis abstracta de orden superior-}
instance Show Expr where
    show e = case e of
        (V x) -> "V[" ++ x ++ "]"
        (I n) -> "N[" ++ (show n) ++ "]"
        (B b) -> "B[" ++ (show b) ++ "]"
        (Add e1 e2) -> "Sum(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Mul e1 e2) -> "Prod(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Succ n) -> "Succ(" ++ (show n) ++ ")"
        (Pred n) -> "Pred(" ++ (show n) ++ ")"
        (Not e) -> "Not(" ++ (show e) ++ ")"
        (And e1 e2) -> "And(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Or e1 e2) -> "Or(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Lt e1 e2) -> "Lt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Gt e1 e2) -> "Gt(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (Eq e1 e2) -> "Eq(" ++ (show e1) ++ ", " ++ (show e2) ++ ")"
        (If e1 e2 e3) -> "If(" ++ (show e1) ++ ", " ++ (show e2) ++ ", " ++ (show e3) ++ ")"
        (Let v e1 e2) -> "Let(" ++ (show e1) ++ ", " ++ (show v) ++ "." ++ (show e2) ++ ")"
        (Fn v e) -> "\\"++v++"->"++(show e)
        (App e1 e2) -> (show e1)++" "++(show e2)

type Substitution = (Identifier, Expr)

{-Obtiene el conjunto de variables libres de una expresion-}
frVars :: Expr -> [Identifier]
frVars (V x) = [x]
frVars (I n) = []
frVars (B b) = []
frVars (Add e1 e2) = union (frVars e1) (frVars e2)
frVars (Mul e1 e2) = union (frVars e1) (frVars e2)
frVars (Succ n) = []
frVars (Pred n) = []
frVars (Not b) = []
frVars (And b1 b2) = union (frVars b1) (frVars b2)
frVars (Or e1 e2) = union (frVars e1) (frVars e2)
frVars (Lt e1 e2) = union (frVars e1) (frVars e2)
frVars (Gt e1 e2) = union (frVars e1) (frVars e2)
frVars (Eq e1 e2) = union (frVars e1) (frVars e2)
frVars (If e1 e2 e3) = (frVars e1) ++ (frVars e2) ++ (frVars e3)
frVars (Let v e1 e2) = union (frVars e1) (frVars e2) \\ [v]
frVars (Fn v e) = (frVars e) \\ [v]
frVars (App e1 e2) = (union (frVars e1) (frVars e2))


{- Aplica la sustitucion de expresion dado en caso de ser posible -}
subst :: Expr -> Substitution -> Expr
subst e sub@(v, s) = case e of
    (V x) ->
        if (x == v) then s
        else (V x)
    (I n) -> (I n)
    (B b) -> (B b)
    (Add e1 e2) -> Add (subst e1 sub) (subst e2 sub)
    (Mul e1 e2) -> Mul (subst e1 sub) (subst e2 sub)
    (Succ e) -> Succ (subst e sub)
    (Pred e) -> Pred (subst e sub)
    (Not b) -> Not (subst b sub)
    (And e1 e2) -> And (subst e1 sub) (subst e2 sub)
    (Or e1 e2) -> Or (subst e1 sub) (subst e2 sub)
    (Lt e1 e2) -> Lt (subst e1 sub) (subst e2 sub)
    (Gt e1 e2) -> Gt (subst e1 sub) (subst e2 sub)
    (Eq e1 e2) -> Eq (subst e1 sub) (subst e2 sub)
    (If e1 e2 e3) -> If (subst e1 sub) (subst e2 sub) (subst e3 sub)
    (Let lv e1 e2) ->
        if (lv == v) then error "Variable Error"
        else if (elem lv (frVars (s))) then error "Could not apply the substitution"
        else  Let lv (subst e1 sub) (subst e2 sub)
    (Fn lv e) ->
        if (lv == v) || (elem lv (frVars (s))) then (subst e sub)
        else (Fn lv (subst e sub))
    (App e1 e2) -> (App (subst e1 sub) (subst e2 sub))

incrVar :: Identifier -> Identifier
incrVar v = (incrVarAux v)

alphaExpr :: Expr -> Expr
alphaExpr (V v) = (V (incrVar v))
alphaExpr (Fn v e)
    | (elem v (frVars e)) = (Fn (incrVar v) (alphaExpr (alphaExprAux v e)))
    | otherwise = (Fn v (alphaExpr e))
alphaExpr (App e1 e2) = (App (alphaExpr e1) (alphaExpr e2))

incrVarAux :: String -> String
incrVarAux s = (reverse (sacaString (reverse s))) ++ (show (strToInt (sacaInt (reverse s))))

sacaString :: String -> String
sacaString [] = []
sacaString (c:cs)
    | (isDigit c) = (sacaString cs)
    | otherwise = (c:cs)

sacaInt :: String -> String
sacaInt [] = []
sacaInt (c:cs)
    | (isDigit c) = [c] ++ (sacaInt cs)
    | otherwise = []

strToInt :: String -> Int
strToInt [] = 1
strToInt (x:[]) = (digitToInt x) + 1
strToInt (x:xs) = (10*(strToInt xs)) + (digitToInt x)

alphaExprAux :: Identifier -> Expr -> Expr
alphaExprAux [] _ = error "Invalid parameter"
alphaExprAux v (V u)
    | v == u = (V (incrVar u))
    | otherwise = (V u)
alphaExprAux v (Fn u e)
    | (elem v (frVars e)) = (Fn u (alphaExprAux v e))
    | otherwise = (Fn u e)
alphaExprAux v (App e1 e2)
    | ((elem v (frVars e1)) && (elem v (frVars e2))) = (App (alphaExprAux v e1) (alphaExprAux v e1))
    | (elem v (frVars e1)) = (App (alphaExprAux v e1) e2)
    | (elem v (frVars e1)) = (App e1 (alphaExprAux v e2))
    | otherwise = (App e1 e2)

beta :: Expr -> Expr
beta e = case e of
    V v -> V v
    Fn v e -> (Fn v (beta e))
    App e1 e2 ->
      case (beta e1) of
        (Fn v1 e1') -> (subst e1' (v1, (beta e2)))
        _ -> App (beta e1) (beta e2)

normal :: Expr -> Bool
normal (V _) = True
normal (I _) = True
normal (B _) = True
normal (Fn _ e) = (normal e)
normal _ = False

{-Determinamos si dos expresiones son alfa equivalentes-}
alphaEq :: Expr -> Expr -> Bool
alphaEq (V x) (V y) = x == y
alphaEq (I n) (I m) = n == m
alphaEq (B b1) (B b2) = b1 == b2
alphaEq (Add e1 e2) (Add d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)
alphaEq (Mul e1 e2) (Mul d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)
alphaEq (Succ e1) (Succ e2) = alphaEq e1 e2
alphaEq (Pred e1) (Pred e2) = alphaEq e1 e2
alphaEq (Not e1) (Not e2) = alphaEq e1 e2
alphaEq (And e1 e2) (And d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)
alphaEq (Or e1 e2) (Or d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)
alphaEq (Lt e1 e2) (Lt d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)
alphaEq (Gt e1 e2) (Gt d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)
alphaEq (Eq e1 e2) (Eq d1 d2) = (alphaEq e1 d1) && (alphaEq e2 d2)
alphaEq (If e1 e2 e3) (If d1 d2 d3) = (alphaEq e1 d1) && (alphaEq e2 d2) && (alphaEq e3 d3)
alphaEq (Let x e1 e2) (Let y d1 d2) =
    if(x == y) then (alphaEq e1 d1) && (alphaEq e2 d2)
    else False
alphaEq _ _ = False
