-- Falta Frame de Let e If

module BAE.Dynamic where

import Data.List
import BAE.Sintax as Sintax
import BAE.Type as Type

type Pending = ()
data Frame = FnF Identifier Pending
           | AddFL Pending Expr
           | AddFR Expr Pending
           | MulFL Pending Expr
           | MulFR Expr Pending
           | SuccF Pending
           | PredF Pending
           | NotF Pending
           | AndFL Pending Expr
           | AndFR Expr Pending
           | OrFL Pending Expr
           | OrFR Expr Pending
           | LtFL Pending Expr
           | LtFR Expr Pending
           | GtFL Pending Expr
           | GtFR Expr Pending
           | EqFL Pending Expr
           | EqFR Expr Pending
           | IfF Pending Expr Expr
           | Let
           | Fn
           | AppFL Pending Expr
           | AppFR Expr Pending
           | Alloc Pending
           | Deref Pending
           | AssigFL Pending Expr
           | AssigFR Expr Pending
           | SeqFL Pending Expr
           | SeqFR Expr Pending
           | WhileFL Pending Expr
           | WhileFR Expr Pending

instance Show Frame where
    show e = case e of
        (AddFL p e2) -> "Sum(-, " ++ (show e2) ++ ")"
        (AddFR e1 p) -> "Sum(" ++ (show e1) ++"-)"
        (MulFL p e2) -> "Mul(-, " ++ (show e2) ++ ")"
        (MulFR e1 p) -> "Mul(" ++ (show e1) ++"-)"
        (Succ n) -> "Succ(-)"
        (Pred n) -> "Pred(-)"
        (Not e) -> "Not(-)"
        (AndFL p e2) -> "And(-, " ++ (show e2) ++ ")"
        (AndFR e1 p) -> "And(" ++ (show e1) ++"-)"
        (OrFL p e2) -> "Or(-, " ++ (show e2) ++ ")"
        (OrFR e1 p) -> "Or(" ++ (show e1) ++"-)"
        (LtFL p e2) -> "Lt(-, " ++ (show e2) ++ ")"
        (LtFR e1 p) -> "Lt(" ++ (show e1) ++"-)"
        (GtFL p e2) -> "Gt(-, " ++ (show e2) ++ ")"
        (GtFR e1 p) -> "Gt(" ++ (show e1) ++"-)"
        (EqFL p e2) -> "Eq(-, " ++ (show e2) ++ ")"
        (EqFR e1 p) -> "Eq(" ++ (show e1) ++"-)"
        (If e1 e2 e3) -> "If(-," ++ (show e2) ++ ", " ++ (show e3) ++ ")"
        (Let v e1 e2) -> "Let(" ++ (show e1) ++ ", " ++ (show v) ++ "." ++ (show e2) ++ ")"
        (Fn v e) -> "\\"++v++"->"++(show e)
        (AppFL p e2) -> "App(-, " ++ (show e2) ++ ")"
        (AppFR e1 p) -> "App(" ++ (show e1) ++"-)"
        (L n) -> "L "++ (show n)
        Void -> "Void"
        (Alloc n) -> "Alloc(-)"
        (Deref e) -> "Deref(-)"
        (AssigFL p e2) -> "Assig(-, " ++ (show e2) ++ ")"
        (AssigFR e1 p) -> "Assig(" ++ (show e1) ++"-)"
        (SeqFL p e2) -> "Seq(-, " ++ (show e2) ++ ")"
        (SeqFR e1 p) -> "Seq(" ++ (show e1) ++"-)"
        (WhileFL p e2) -> "While(-, " ++ (show e2) ++ ")"
        (WhileFR e1 p) -> "While(" ++ (show e1) ++"-)"


-- Para alphaEq vamos a decir que los marcos son iguales.




{-Funcion que recibe un expresion y devuelve e -> e', tal que no esta bloqueado, y si lo es, manda error -}
eval1 :: Memory -> Expr -> (Memory, Expr)
eval1 k (V x) = (k, (V x))
eval1 k (I n) = (k, (I n))
eval1 k (B b) = (k, (B b))
eval1 k (Add (I n) (I m)) = (k, (I (n + m)))
eval1 k (Add (I n) e2) = (k, (Add (I n) (eval1 k e2)))
eval1 k (Add e1 e2) = (k, (Add (eval1 k e1) e2))
eval1 k (Mul (I n) (I m)) = (k, (I (n + m)))
eval1 k (Mul (I n) e2) = (k, (Mul (I n) (eval1 k e2)))
eval1 k (Mul e1 e2) = (k, (Mul (eval1 k e1) e2))
eval1 k (Succ (I n)) = (k, (I (n + 1)))
eval1 k (Succ e) = (k, (eval1 k e))
eval1 k (Pred (I 0)) = error "eval1 Pred: El cero no tiene predecesor."
eval1 k (Pred (I n)) = (k, (I (n - 1)))
eval1 k (Pred e) = (k, (eval1 k e))
eval1 k (Not (B True)) = (k, (B False))
eval1 k (Not (B False)) = (k, (B True))
eval1 k (Not e) = (k, (NOT (eval1 k e)))
eval1 k (And (B b) (B c) = (k, (B (b && c)))
eval1 k (And (B b) e2) = (k, (And (B b) (eval1 k e2)))
eval1 k (And e1 e2) = (k, (And (eval1 k e1) e2))
eval1 k (Or (B b) (B c) = (k, (B (b || c)))
eval1 k (Or (B b) e2) = (k, (Or (B b) (eval1 k e2)))
eval1 k (Or e1 e2) = (k, (Or (eval1 k e1) e2))
eval1 k (Lt (I n) (I m)) = (k, (B (n < m)))
eval1 k (Lt (I n) e2) = (k, (Lt (I n) (eval1 k e2)))
eval1 k (Lt e1 e2) = (k, (Lt (eval1 k e1) e2))
eval1 k (Gt (I n) (I m)) = (k, (B (n > m)))
eval1 k (Gt (I n) e2) = (k, (Gt (I n) (eval1 k e2)))
eval1 k (Gt e1 e2) = (k, (Gt (eval1 k e1) e2))
eval1 k (Eq (I n) (I m)) = (k, (B (n == m)))
eval1 k (Eq (I n) e2) = (k, (Eq (I n) (eval1 k e2)))
eval1 k (Eq e1 e2) = (k, (Eq (eval1 k e1) e2))
eval1 k (If (B True) e1 e2) = (k, e1)
eval1 k (If (B False) e1 e2) = (k, e2)
eval1 k (If e1 e2 e3) = (k, (If (eval1 k e1) e2 e3))
eval1 k (Let v e1 e2)
    | (isValor e1) = (k, (subst e2 (v, e1)))
    | otherwise = (k, (Let v (eval1 k e1) e2))
eval1 k (Fn v e)
    | isValor e = (k, (fn v e))
    | otherwise = (k, (Fn v (eval1 k e)))
eval1 k (App (Fn v e) e2)
    | isValor e = (k, (Fn))
eval1 k (App e1 e2)
    | isValor e1 = (k, (App e1 (eval1 k e2)))
    | not (normal e2) = (eval1 k e2)
    | otherwise = error "Necesita un funcion para App"
eval1 k (L n) = (L n)
eval1

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






































normal :: Expr -> Bool
normal fix = false

locked :: Expr -> Bool
locked (Fix x e) = Falses
locked (Let e1 e2) = locked e1

evale :: Expr -> alphaExpr
        (Fix x e) = (Fix x e)




-- A la derecha hay que satisfacer algo, a la izquierda es el contexto.
