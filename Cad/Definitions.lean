import Mathlib
namespace Definitions
-- Esse arquivo contém as definições necessárias para
-- resolver o problema de uma forma computável
structure Elem (numVars : Nat) where
  var : Fin numVars
  exp : Nat

structure MyMonomial (numVars : Nat) where
  coef : ℚ
  vars : List (Elem numVars)

structure MyPolynomial (numVars : Nat) where
  monoms : List (MyMonomial numVars)

-- Definições úteis
/- def zero : List MyMonomial := [{coef := 0, vars := []}] -/
/- def const_one : MyMonomial := MyMonomial.mk 1 [] -/

/- -- Função auxiliar que encontra o maior expoente de um monômio -/
/- def greatest_ex (aux : Elem) : List Elem → Elem -/
/- | [] => aux -/
/- | p::ps => -/
/-   if p.exp ≥ aux.exp then greatest_ex p ps -/
/-   else greatest_ex aux ps -/

/- -- Função que verifica se determinada entrada é um polinômio de grau zero -/
/- def zero_degree : List MyMonomial → Bool -/
/- | [] => true -/
/- | p::ps => -/
/-     if p.vars.any (fun vp => vp.exp ≠ 0) then false -/
/-     else zero_degree ps -/

/- -- Função que verifica se duas listas de elementos são iguais (independe da ordem) -/
/- -- Pra melhorar a complexidade: ao invés de fazer isso, poderia ordenar os monômios com as variáveis por ordem alfabética ou algo do tipo? -/
/- def vars_equality (P Q : List Elem): Bool := -/
/-   -- Verifica se todos os elementos de Q têm correspondentes em P -/
/-   Q.all (fun e1 => -/
/-     match P.find? (fun e2 => e1.var = e2.var ∧ e1.exp = e2.exp) with -/
/-     | some _ => true -/
/-     | none => false -/
/-   ) ∧ -/
/-   -- Verifica se todos os elementos de P têm correspondentes em Q -/
/-   P.all (fun e1 => -/
/-     match Q.find? (fun e2 => e1.var = e2.var ∧ e1.exp = e2.exp) with -/
/-     | some _ => true -/
/-     | none => false -/
/-   ) -/

/- -- Função que verifica se dois polinômios são iguais (independe da ordem) -/
/- -- também pode ser melhorada se os polinômios já estiverem ordenados -/
/- def Poly_eq (P Q : List MyMonomial): Bool := -/
/-   Q.all (fun e1 => -/
/-     match P.find? (fun e2 => e1.coef = e2.coef ∧ (vars_equality e1.vars e2.vars)) with -/
/-     | some _ => true -/
/-     | none => false -/
/-   ) ∧ P.all (fun e1 => -/
/-     match Q.find? (fun e2 => e1.coef = e2.coef ∧ (vars_equality e1.vars e2.vars)) with -/
/-     | some _ => true -/
/-     | none => false) -/

/- -- Função que ajuda a atualizar os coeficientes dos termos semelhantes da adição -/
/- def update_monomial (p : MyMonomial) : List MyMonomial → List MyMonomial -/
/- | [] => [] -/
/- | q::qs => -/
/-   if vars_equality p.vars q.vars then -/
/-     if p.coef + q.coef ≠ 0 then -/
/-       { coef := p.coef + q.coef, vars := q.vars } :: qs -/
/-     else qs -/
/-   else -/
/-     q::(update_monomial p qs) -/

/- -- Define a adição de polinômios: -/
/- def addition : List MyMonomial → List MyMonomial → List MyMonomial -/
/- | [], Q => Q -/
/- | p::ps, Q => -/
/-     if Q.any (fun q => vars_equality q.vars p.vars) then -/
/-       addition ps (update_monomial p Q) -/
/-     else addition ps (p::Q) -/

/- -- Função auxiliar, que reduz cada monômio (mod <B>) -/
/- -- X^n = X(mod <B>) ∀ n ≥ 2 -/
/- def reductionmon_mod_B (M : MyMonomial) : MyMonomial := -/
/-   let reduced_vars := M.vars.map (fun ex => -/
/-     if ex.exp ≥ 2 then -/
/-       -- Se o expoente for maior ou igual a 2, reduz para 1 (mod X^2 - X) -/
/-       { var := ex.var, exp := 1 } -/
/-     else -/
/-       -- Mantém o termo se o expoente for 1 ou 0 -/
/-       ex -/
/-   ) -/
/-   -- Retorna o monômio com coeficiente inalterado e variáveis reduzidas -/
/-   { coef := M.coef, vars := reduced_vars } -/

/- -- Reduz o polinômio (mod <B>) -/
/- def reductionpoly_mod_B : List MyMonomial → List MyMonomial -/
/- | [] => [] -/
/- | p::ps => -/
/-     let exp : Elem := greatest_ex (Elem.mk 0 0) p.vars -/
/-     -- usa da adição para agrupar possíveis termos semelhantes: -/
/-     if exp.exp < 2 then addition [p] (reductionpoly_mod_B ps) -/
/-     else addition [reductionmon_mod_B p] (reductionpoly_mod_B ps) -/

/- -- Multiplicação de dois monômios -/
/- def monomial_multiply (m1 m2 : MyMonomial) : MyMonomial := -/
/-   let new_coef := m1.coef * m2.coef -/
/-   let combined_vars := -/
/-     m1.vars.map (fun e1 => -/
/-       match m2.vars.find? (fun e2 => e1.var = e2.var) with -/
/-       | some e2 => { var := e1.var, exp := e1.exp + e2.exp } -/
/-       | none => e1 -/
/-     ) ++ m2.vars.filter (fun e2 => m1.vars.all (fun e1 => e1.var ≠ e2.var)) -- adiciona as variáveis de m2 que não estão em m1 -/
/-   { coef := new_coef, vars := combined_vars } -/

/- -- Multiplicação de um monômio por um polinômio -/
/- def mul_monomial_by_polynomial (m : MyMonomial) : List MyMonomial → List MyMonomial -/
/- | [] => [] -/
/-  -- garante que um mesmo polinômio não vai ter mesmas variáveis e expoentes em mais de uma posição da lista: -/
/- | q::qs => addition [monomial_multiply m q] (mul_monomial_by_polynomial m qs) -/

/- -- Função de multiplicação de dois polinômios -/
/- def multiplication : List MyMonomial → List MyMonomial → List MyMonomial -/
/- | [], _ => [] -/
/- | p::ps, Q => -/
/-   let product_p := mul_monomial_by_polynomial p Q -/
/-   let rest_product := multiplication ps Q -/
/-   -- usa a função de adição para combinar os resultados -/
/-   addition product_p rest_product -/

/- -- Função que verifica se uma variável pertence ao conjunto de variáveis do polinômio -/
/- def isVar (v:Nat) (G: List MyMonomial) : Bool := -/
/-   if  G.any (fun G' => -/
/-     if G'.vars.any (fun g => g.var = v) then true -/
/-     else false) then true else false -/

/- -- Função auxiliar que pega a primeira variável do monômio -/
/- def getVar : List Elem → Nat -/
/- | [] => 0 -/
/- | f::_=> f.var -/

/- -- Função que verifica se a regra de extensão foi devidamente aplicada -/
/- def check_extension : List MyMonomial →  Bool -/
/- | [] => true -/
/- | p::ps => -/
/-   if (isVar (getVar p.vars) ps) then false -/
/-   else -/
/-     let p_red : List MyMonomial := reductionpoly_mod_B ps -/
/-     if Poly_eq p_red ps then true else false -/

/- -- Define função de negação -/
/- def f (z : String) : List MyMonomial := [MyMonomial.mk (-1) [Elem.mk z 1], const_one] -/

@[simp]
def evalElems (numVars : Nat) : List (Elem numVars) → (Vector ℝ numVars) → ℝ
  | [], vals => 1
  | elem :: elems, vals =>
    vals[elem.var] ^ elem.exp * evalElems numVars elems vals

@[simp]
def evalMonom (numVars : Nat) : (MyMonomial numVars) → (Vector ℝ numVars) → ℝ := fun { coef, vars } vals =>
  coef * evalElems numVars vars vals

@[simp]
def evalPoly (numVars : Nat) : (p : MyPolynomial numVars) → (Vector ℝ numVars) → ℝ := fun p vals =>
  match hP: p.monoms with
  | [] => 0
  | monom :: monoms =>
    have h2 : monoms.length < p.monoms.length := by rw [hP]; simp
    evalMonom numVars monom vals + evalPoly numVars { monoms } vals
  termination_by p => p.monoms.length

/- theorem evalPoly_id : ∀ p : MyPolynomial, ∀ vals, evalPoly p va -/

def M : MyMonomial 1 := { coef := 2, vars := [ { var := 0, exp := 1 } ] }
def vals : Vector ℝ 1 := #[3].toVector
def P : MyPolynomial 1 := { monoms := [M] }

example : evalMonom 1 M vals > 0 := by simp [M, vals]

#eval evalPoly 1 P vals

example : evalPoly 1 P vals > 0 := by rw [P, evalPoly]; simp [M, vals]
example : evalPoly 1 P vals = 6 := by rw [P, evalPoly]; simp [M, vals]; linarith

def isRoot (numVars : Nat) (p : MyPolynomial numVars) (rs : Vector ℝ numVars) : Prop := evalPoly numVars p rs = 0

end Definitions
