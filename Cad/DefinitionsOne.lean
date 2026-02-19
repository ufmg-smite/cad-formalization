import Mathlib
namespace Definitions
-- Esse arquivo contém as definições necessárias para
-- resolver o problema de uma forma computável

structure CMonomial where
  coef : ℚ
  exp : Nat

instance : ToString CMonomial where
  toString m :=
    let pref := if m.coef = 1 then "" else toString m.coef ++ " * "
    let suff := if m.exp = 1 then "" else " ^ " ++ (toString m.exp)
    pref ++ "x" ++ suff

def CPolynomial := List CMonomial

instance : ToString CPolynomial where
  toString ms :=
    let ms' := ms.map toString
    if ms'.isEmpty then ""
    else
      String.intercalate " + " ms'

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

/- @[simp] -/
/- def evalElems : List Elem → (Vector ℝ numVars) → ℝ -/
/-   | [], vals => 1 -/
/-   | elem :: elems, vals => -/
/-     vals[elem.var] ^ elem.exp * evalElems numVars elems vals -/

@[simp]
def evalMonom : CMonomial → ℝ → ℝ := fun { coef, exp } r =>
  coef * r ^ exp

@[simp]
def evalPoly : (p : CPolynomial) → ℝ → ℝ := fun p r =>
  match p with
  | [] => 0
  | monom :: monoms =>
    evalMonom monom r + evalPoly monoms r

def M : CMonomial := { coef := 2, exp := 1 }
def r : Real := 3
def P : CPolynomial := [M]

example : evalMonom M 3 > 0 := by simp [M, r]
example : evalPoly P r > 0 := by simp [P, M, r]
example : evalPoly P r = 6 := by simp [P, M, r]; linarith

def isRoot (p : CPolynomial) (r : Real) : Prop := evalPoly p r = 0

@[simp]
noncomputable def monom_toMathlib (m : CMonomial) : Polynomial ℝ :=
  Polynomial.C (m.coef : ℝ) * Polynomial.X ^ m.exp

@[simp]
noncomputable def poly_toMathlib (p : CPolynomial) : Polynomial ℝ :=
  match p with
  | [] => Polynomial.C 0
  | monom :: monoms =>
    monom_toMathlib monom + poly_toMathlib monoms

theorem evalsMonomial : ∀ m : CMonomial, ∀ r : ℝ, (monom_toMathlib m).eval r = evalMonom m r := by
  intros m r
  simp

example (p q : Polynomial ℝ) (r : ℝ) : Polynomial.eval r (p + q) = Polynomial.eval r p + Polynomial.eval r q := Polynomial.eval_add

theorem evals : ∀ p : CPolynomial, ∀ r : ℝ, (poly_toMathlib p).eval r = evalPoly p r := by
  intros p r
  induction p
  next =>
    simp
  next monom monoms IH =>
    simp only [evalPoly, poly_toMathlib]
    rw [<- IH, Polynomial.eval_add, evalsMonomial]

theorem roots : ∀ p : CPolynomial, ∀ r : ℝ, (poly_toMathlib p).IsRoot r → isRoot p r := by
  intros p r hP
  rw [Polynomial.IsRoot, evals p r] at hP
  rw [isRoot]
  exact hP

theorem roots_interval: ∀ p : CPolynomial, ∀ (a b r: ℝ), r >= a ∧ r <= b ∧ (poly_toMathlib p).IsRoot r -> ∃r' : ℝ, r' >= a ∧ r' <= b ∧ isRoot p r' := by
  intros p a b r hr
  obtain ⟨hra, hrb, hr_root⟩ := hr
  apply roots p r at hr_root
  exact Exists.intro r ⟨hra, hrb, hr_root⟩

theorem exists_root_interval: ∀ p: CPolynomial, ∀ (a b : ℝ), a <= b → evalPoly p a <= 0 → 0 <= evalPoly p b -> ∃ r: ℝ, r >= a ∧ r <= b ∧ isRoot p r := by
  intros p a b hab ha hb
  let f_p := fun x => (poly_toMathlib p).eval x
  have p_continuous : ContinuousOn f_p (Set.Icc a b) := by exact (poly_toMathlib p).continuousOn
  have poly_mathlib_root : ∃ r: ℝ, r >= a ∧ r <= b ∧ (poly_toMathlib p).IsRoot r := by
    have intermediate_value_app := intermediate_value_Icc hab p_continuous
    have zero_in_image : 0 ∈ f_p '' Set.Icc a b := by
      have zab : 0 ∈ Set.Icc (f_p a) (f_p b) := by
        rw [<- evals p a] at ha; rw [<- evals p b] at hb
        exact ⟨ha, hb⟩
      exact Set.mem_of_mem_of_subset zab intermediate_value_app
    obtain ⟨x, ⟨hxa, hxb⟩, hx_root⟩ := zero_in_image
    exact Exists.intro x ⟨hxa, hxb, hx_root⟩
  obtain ⟨r, hra, hrb, hr_root⟩ := poly_mathlib_root
  apply (roots_interval p a b r ⟨hra, hrb, hr_root⟩)
end Definitions

noncomputable def FinsetToOrderedList (s : Finset ℝ) : List ℝ := s.sort

open Polynomial
theorem no_roots_between_roots (p : Polynomial ℝ) (hp : p ≠ 0) : ∀ i < (p.roots.toFinset.sort (· ≤ ·)).length - 1,
  ¬∃ x : ℝ , x ∈ Set.Ioo (p.roots.toFinset.sort (· ≤ ·))[i]! (p.roots.toFinset.sort (· ≤ ·))[i+1]! ∧
  p.eval x = 0 := by
  intro i hi
  by_contra h
  obtain ⟨x, ⟨hxi, hxi1⟩, hx_root⟩ := h

  have h_roots : x ∈ p.roots := by simp_all
  have hx_mem_sorted : x ∈ p.roots.toFinset.sort (· ≤ ·) := by simpa using h_roots
  have x_in : x ∈ p.roots.toList := by simp_all
  have x_in : x ∈ p.roots.sort := by simp_all
  have x_in : x ∈ p.roots.toFinset.sort := by simp_all

  have F := (List.exists_mem_iff_getElem (l := p.roots.toFinset.sort) (p := fun y => y = x)).mp (by use x)

  have h_index : ∃ j : Fin ((p.roots.toFinset.sort (· ≤ ·)).length), x = (p.roots.toFinset.sort (· ≤ ·))[j] := by
    simp at F
    obtain ⟨i, hi⟩ := F
    obtain ⟨h1, h2⟩ := hi
    have : p.roots.toFinset.card = p.roots.toFinset.sort.length := Eq.symm (Finset.length_sort fun a b => a ≤ b)
    use ⟨i, by grind⟩
    simp
    grind

  obtain ⟨j, hj⟩ := h_index

  have contr1 : j > i := by
    by_contra h
    have hj1 : j ≤ i := by linarith
    rw[hj] at hxi1
    have hmono :
      (p.roots.toFinset.sort (· ≤ ·))[i] ≥
      (p.roots.toFinset.sort (· ≤ ·))[j] := by
      have := List.pairwise_iff (· ≤ ·) (p.roots.toFinset.sort (· ≤ ·))
      simp_all only [Fin.getElem_fin]
      have hsorted2 : (p.roots.toFinset.sort (· ≤ ·)).SortedLT := by
        exact Finset.sortedLT_sort p.roots.toFinset
      apply (StrictMono.le_iff_le (Finset.sortedLT_sort p.roots.toFinset)).mpr
      grind
    have hcontra : (p.roots.toFinset.sort (· ≤ ·))[j] < (p.roots.toFinset.sort (· ≤ ·))[j] := by
      simp_all
      grind
    exact lt_irrefl _ hcontra

  have contr2 : j < i + 1 := by
    by_contra h
    have hj1 : j ≥ i + 1 := by linarith
    rw[hj] at hxi1
    have hmono :
      (p.roots.toFinset.sort (· ≤ ·))[i+1] ≤
      (p.roots.toFinset.sort (· ≤ ·))[j] := by
      have := List.pairwise_iff (· ≤ ·) (p.roots.toFinset.sort (· ≤ ·))
      simp_all only [Fin.getElem_fin]
      have hsorted2 : (p.roots.toFinset.sort (· ≤ ·)).SortedLT := by
        exact Finset.sortedLT_sort p.roots.toFinset

      apply (StrictMono.le_iff_le (Finset.sortedLT_sort p.roots.toFinset)).mpr
      grind
    have hcontra : (p.roots.toFinset.sort (· ≤ ·))[j] < (p.roots.toFinset.sort (· ≤ ·))[j] := by
      simp_all
      grind
    exact lt_irrefl _ hcontra

  linarith

-- Em um intervalo que o polinômio não tem raízes, se o sinal de um polinomio é positivo em um ponto do intervalo, então ele é sempre positivo
theorem sign_stops (p : Polynomial ℝ) (hp : p ≠ 0) (a b : ℝ) (hab : a ≤ b) : (∀ x : ℝ, x ∈ Set.Ioo a b → ¬p.IsRoot x) → (p.eval x > 0 → ∀ y : ℝ, y ∈ Set.Ioo a b → p.eval y > 0) := by
  intro h_no_root hpos y hy

  by_contra hneg

  have hle : eval y p ≤ 0 := not_lt.mp hneg

  have hx_le : x ≤ y ∨ y ≤ x := le_total x y
  rcases hx_le with hxy | hyx

  ·
    -- eval x p > eval y p
    -- y > x
    -- Icc x y
    have hroot : ∃ c ∈ Set.Ioo a b, eval c p = 0 := by
      have hsign_change : (eval x p) * (eval y p) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) hle

      have hcont : Continuous fun t => eval t p := Polynomial.continuous p
      have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc x y) :=
        (Polynomial.continuous p).continuousOn

      have := intermediate_value_Icc hxy hcont2
      have zero_in_interval : 0 ∈ Set.Icc (eval y p) (eval x p) := by
        sorry

      sorry
    rcases hroot with ⟨c, hcIoo, hc⟩

    have : p.IsRoot c := by
      simp [Polynomial.IsRoot, hc]

    exact h_no_root c hcIoo this
  ·
    -- eval x p > eval y p
    -- x > y
    -- Icc y x
    have hroot :
    ∃ c ∈ Set.Ioo a b, eval c p = 0 := by

      have hsign_change : (eval x p) * (eval y p) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) hle

      have hcont : Continuous fun t => eval t p := Polynomial.continuous p
      have hcont2 : ContinuousOn (fun t => p.eval t) (Set.Icc y x) :=
        (Polynomial.continuous p).continuousOn

      have := intermediate_value_Icc hyx hcont2

      have zero_in_interval : 0 ∈ Set.Icc (eval y p) (eval x p) := by
        sorry

      sorry
    rcases hroot with ⟨c, hcIoo, hc⟩

    have : p.IsRoot c := by
      simp [Polynomial.IsRoot, hc]

    exact h_no_root c hcIoo this
