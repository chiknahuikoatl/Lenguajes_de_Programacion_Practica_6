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

{-Funcion que recibe un expresion y devuelve e -> e', tal que no esta bloqueado, y si lo es, manda error -}
eval1 :: Expr -> Expr
eval1 (V x) = (V x)
eval1 (I n) = (I n)
eval1 (B True) = (B True)
eval1 (B False) = (B False)
eval1 (Add (I n) (I m)) = (I (n + m))
eval1 (Add (I n) e2) = (eval1 e2)
eval1 (Add e1 e2) = (eval1 e1)
eval1 (Mul (I n) (I m)) = (I (n * m))
eval1 (Mul (I n) e2) = (eval1 e2)
eval1 (Mul e1 e2) = (eval1 e1)
eval1 (Succ (I n)) = (I (n + 1))
eval1 (Succ e) = (eval1 e)
eval1 (Pred (I n)) = (I (n - 1))
eval1 (Pred e) = (eval1 e)
eval1 (Not (B True)) = (B False)
eval1 (Not (B False)) = (B True)
eval1 (Not e) = (eval1 e)
eval1 (And (B True) (B True)) = (B True)
eval1 (And (B True) (B False)) = (B False)
eval1 (And (B False) (B True)) = (B False)
eval1 (And (B False) (B False)) = (B False)
eval1 (And (B False) e2) = (eval1 e2)
eval1 (And (B True) e2) = (eval1 e2)
eval1 (And e1 e2) = (eval1 e1)
eval1 (Or (B True) (B True)) = (B True)
eval1 (Or (B True) (B False)) = (B True)
eval1 (Or (B False) (B True)) = (B True)
eval1 (Or (B False) (B False)) = (B False)
eval1 (Or (B False) e2) = (eval1 e2)
eval1 (Or (B True) e2) = (eval1 e2)
eval1 (Or e1 e2) = (eval1 e1)
eval1 (Lt (I n) (I m))
    | (n >= m) = (B False)
    | otherwise = (B True)
eval1 (Lt (I n) e2) = (eval1 e2)
eval1 (Lt e1 e2) = (eval1 e1)
eval1 (Gt (I n) (I m))
    |  (n <= m) = (B False)
    | otherwise = (B False)
eval1 (Gt (I n) e2) = (eval1 e2)
eval1 (Gt e1 e2) = (eval1 e1)
eval1 (Eq (I n) (I m))
    |  (n == m) = (B True)
    | otherwise = (B False)
eval1 (Eq (I n) e2) = (eval1 e2)
eval1 (Eq e1 e2) = (eval1 e1)
eval1 (If (B True) e1 e2) = e1
eval1 (If (B False) e1 e2) = e2
eval1 (If e1 e2 e3) = (If (eval1 e1) e2 e3)
eval1 (Let v e1 e2) = eval1 (subst e1 (v, e2))
eval1 (Fn v e) = (eval1 (e))
eval1 (App e1 e2)
    | not (normal e1) = (eval1 e1)
    | not (normal e2) = (eval1 e2)
    | otherwise = error "Necesita un funcion para App"

{-Funcion que recibe un expresion y regresa e -> e', aunque esta bloqueado -}
evalAux :: Expr -> Expr
evalAux (V x) = (V x)
evalAux (I n) = (I n)
evalAux (B True) = (B True)
evalAux (B False) = (B False)
evalAux (Add (I n) (I m)) = (I (n + m))
evalAux (Add e1 e2) = (Add e1 e2)
evalAux (Mul (I n) (I m)) = (I (n * m))
evalAux (Mul e1 e2) = (Add e1 e2)
evalAux (Succ (I n)) = (I (n + 1))
evalAux (Succ e ) = (Succ e)
evalAux (Pred (I n)) = (I (n - 1))
evalAux (Pred e ) = (Pred e)
evalAux (Not (B True)) = (B False)
evalAux (Not (B False)) = (B True)
evalAux (Not e ) = (Not e)
evalAux (And (B True) (B True)) = (B True)
evalAux (And (B True) (B False)) = (B False)
evalAux (And (B False) (B True)) = (B False)
evalAux (And (B False) (B False)) = (B False)
evalAux (And e1 e2) = (And e1 e2)
evalAux (Or (B True) (B True)) = (B True)
evalAux (Or (B True) (B False)) = (B True)
evalAux (Or (B False) (B True)) = (B True)
evalAux (Or (B False) (B False)) = (B False)
evalAux (Or e1 e2 ) = (Or e1 e2)
evalAux (Lt (I n) (I m))
    | (n >= m) = (B False)
    | otherwise = (B True)
evalAux (Lt e1 e2) = (Lt e1 e2)
evalAux (Gt (I n) (I m))
    |  (n <= m) = (B False)
    | otherwise = (B False)
evalAux (Gt e1 e2) = (Gt e1 e2)
evalAux (Eq (I n) (I m))
    |  (n == m) = (B True)
    | otherwise = (B False)
evalAux (Eq e1 e2) = (Eq e1 e2)
evalAux (If (B True) (I n) (I m)) = (I n)
evalAux (If (B True) (B n) (B m)) = (B n)
evalAux (If (B True) (V n) (V m)) = (V n)
evalAux (If (B False) (I n) (I m)) = (I m)
evalAux (If (B False) (B n) (B m)) = (B m)
evalAux (If (B False) (V n) (V m)) = (V m)
evalAux (If e e1 e2) = (If e e1 e2)
evalAux (Let v e1 e2) = (subst e2 (v, e2))
evalAux (Fn v e) = (evalAux (e))
evalAux (App (Fn v e) e2) = (subst (e) (v, (e2)))
evalAux (App e1 e2) = (App e1 e2)

{-Evalua una expresion aunque no regresa un variable-}
evals :: Expr -> Expr
evals (V x) = (V x)
evals (I n) = (I n)
evals (B True) = (B True)
evals (B False) = (B False)
evals (Add e1 e2) = (evalAux (Add (evals e1) (evals e2)))
evals (Mul e1 e2) = (evalAux (Mul (evals e1) (evals e2)))
evals (Succ e) = (evalAux (Succ (evals e)))
evals (Pred e) = (evalAux (Pred (evals e)))
evals (Not e) = (evalAux (Not (evals e)))
evals (And e1 e2) = (evalAux (And (evals e1) (evals e2)))
evals (Or e1 e2) = (evalAux (Or (evals e1) (evals e2)))
evals (Lt e1 e2) = (evalAux (Lt (evals e1) (evals e2)))
evals (Gt e1 e2) = (evalAux (Gt (evals e1) (evals e2)))
evals (Eq e1 e2) = (evalAux (Eq (evals e1) (evals e2)))
evals (If e1 e2 e3) = (evalAux (If (evals e1) (evals e2) (evals e3)))
evals (Let v e1 e2) = (evals (subst e2 (v, e2)))
evals (Fn v e) = (evals (e))
evals (App (Fn v e1) e2) = (evalAux (subst (evals e1) (v, (evals e2))))
evals (App e1 e2) = (App (evalAux e1) (evalAux e2))


{-Evaua una expresion, manda un error si no regresa un variable-}
evale :: Expr -> Expr
evale (V x) = (V x)
evale (I n) = (I n)
evale (B True) = (B True)
evale (B False) = (B False)
evale (Add e1 e2) = (eval1 (Add (evale e1) (evale e2)))
evale (Mul e1 e2) = (eval1 (Mul (evale e1) (evale e2)))
evale (Succ e) = (eval1 (Succ (evale e)))
evale (Pred e) = (eval1 (Pred (evale e)))
evale (Not e) = (eval1 (Not (evale e)))
evale (And e1 e2) = (eval1 (And (evale e1) (evale e2)))
evale (Or e1 e2) = (eval1 (Or (evale e1) (evale e2)))
evale (Lt e1 e2) = (eval1 (Lt (evale e1) (evale e2)))
evale (Gt e1 e2) = (eval1 (Gt (evale e1) (evale e2)))
evale (Eq e1 e2) = (eval1 (Eq (evale e1) (evale e2)))
evale (If (B True) e2 e3) = (eval1 (evale e2))
evale (If (B False) e2 e3) = (eval1 (evale e3))
evale (If e1 e2 e3) = (eval1 (If (evale e1) e2 e3))
evale (Let v e1 e2) = (eval1 (subst e1 (v, e2)))
evale (Fn v e) = (evale (e))
evale (App (Fn v e1) e2) = (eval1(subst (evale e1) (v, (evale e2))))

isValor :: Expr -> Bool
isValor e
	| e == (I n) = True
	| e == (B n) = True
	| e == (V n) = True
	| e == (L n) = True
	|otherwise = False

eval1 :: State -> State
eval1 (E m (xs) e)
	|(isValor e) = (R (m (xs) e)
	|(e == (Add e1 e2)) = (E (m ((AddFL () e2):xs) e1))
	|(e == (AddFL e1 e2) && (e1 == (I _))) = (E (m ((AddFR e1 ()):xs) e2))
	|(e == (AddFL e1 e2)) = error "Error a sumar"
	|(e == (Mul e1 e2)) = (E (m ((MulFl () e2):xs) e1))
	|(e == (MulFL e1 e2) && (e1 == (I _))) = (E (m ((MulFR e1 ()):xs) e2))
	|(e == (MulFL e1 e2)) = error "Error a sumar"
	|(e == (Succ e1)) = (E (m ((SuccF ()):xs) e1))
	|(e == (Pred e1)) = (E (m ((PredF ()):xs) e1))
	|(e == (Not e1)) = (E (m ((NotF ()):xs) e1))
	|(e == (And e1 e2)) = (E (m ((AndFL () e2):xs) e1))
	|(e == (AndFL e1 e2) && (e1 == (B _))) = (E (m ((AndFR e1 ()):xs) e2))
	|(e == (AndFL e1 e2)) = error "Error a aplicar and"
	|(e == (Or e1 e2)) = (E (m ((OrFL () e2):xs) e1))
	|(e == (OrFL e1 e2) && (e1 == (B _))) = (E (m ((OrFR e1 ()):xs) e2))
	|(e == (OrFL e1 e2)) = error "Error a aplicar and"
	|(e == (Lt e1 e2)) = (E (m ((LtFL () e2):xs) e1))
	|(e == (LtFL e1 e2) && (e1 == (B _))) = (E (m ((LtFR e1 ()):xs) e2))
	|(e == (LtFL e1 e2)) = error "Error a aplicar less than"
	|(e == (Gt e1 e2)) = (E (m ((GtFL () e2):xs) e1))
	|(e == (GtFL e1 e2) && (e1 == (I _))) = (E (m ((GtFR e1 ()):xs) e2))
	|(e == (GtFL e1 e2)) = error "Error a aplicar greater than"
	|(e == (Eq e1 e2)) = (E (m ((EqFL () e2):xs) e1))
	|(e == (EqFL e1 e2) && (e1 == (I _))) = (E (m ((EqFR e1 ()):xs) e2))
	|(e == (EqFL e1 e2)) = error "Error a aplicar equal"
	|(e == (If e1 e2 e3)) = (E (m ((IfF () e2 e3):xs) e1))
	|(
eval1 (R m (s:xs) e)
	|isValor (e) = case s of
		(AddFL () e2) -> (E (m xs (AddFL e e2)))
		(AddFR e1 ()) -> 
			if ((e1 == (I _) && (e == (I _))) then (E (m xs (eval1 (Add e1 e)))) else error "Error a sumar"
		(MulFL () e2) -> (E (m xs (MulFL e e2)))
		(MulFR e1 ()) -> 
			if ((e1 == (I _) && (e == (I _))) then (E (m xs (eval1 (Mul e1 e)))) else error "Error a multiplicar"
		(SuccF ()) -> if (e == (I _)) then (E (m xs (eval1 (Succ e)))) else error "Error a aplicar succesor"
		(PredF ()) -> if (e == (I _)) then (E (m xs (eval1 (Pred e)))) else error "Error a aplicar predecesso	r"
		(NotF ()) -> if (e == (B _)) then (E (m xs (eval1 (Not e)))) else error "Error a aplicar not"
		(AndFL () e2) -> (E (m xs (AndFL e e2)))
		(AndFR e1 ()) -> 
			if ((e1 == (B _) && (e == (B _))) then (E (m xs (eval1 (And e1 e)))) else error "Error a aplicar and"
		(OrFL () e2) -> (E (m xs (OrFL e e2)))
		(OrFR e1 ()) -> 
			if ((e1 == (B _) && (e == (B _))) then (E (m xs (eval1 (Or e1 e)))) else error "Error a aplicar or"
		(LtFL () e2) -> (E (m xs (LtFL e e2)))
		(LtFR e1 ()) -> 
			if ((e1 == (I _) && (e == (I _))) then (E (m xs (eval1 (Lt e1 e)))) else error "Error a aplicar less than"
		(GtFL () e2) -> (E (m xs (GtFL e e2)))
		(GtFR e1 ()) -> 
			if ((e1 == (I _) && (e == (I _))) then (E (m xs (eval1 (Gt e1 e)))) else error "Error a aplicar less than"
		(EqFL () e2) -> (E (m xs (EqFL e e2)))
		(EqFR e1 ()) -> 
			if ((e1 == (I _) && (e == (I _))) then (E (m xs (eval1 (Eq e1 e)))) else error "Error a aplicar less than"
		(IfF () e2 e3) -> if (e == (B _)) then (E (m xs (if(e == (B True)) then e2 else e2)) else error "Error a aplicar if"
	|otherwise = error "Error"






