import Cad.Multivariate.ProjectionTheorem
import Cad.Multivariate.ProjectionTheorem.DiscrNonzero
import Cad.Multivariate.Brown01

def an_sub (i : Nat) (S: Set (Fin i → ℝ)) : Prop := IsAnalyticSubmanifold S

def an_del (i : Nat) (S : Set (Fin i → ℝ)) (f : Polynomial (MvPolynomial (Fin i) ℝ)) : Prop := AnalyticDelineable f S

def connected (i : Nat) (S : Set (Fin i → ℝ)) : Prop := IsConnected S

def non_null (i : Nat) (S : Set (Fin i → ℝ)) (f : Polynomial (MvPolynomial (Fin i) ℝ)) : Prop :=
  ∀ a ∈ S, specialize f a ≠ 0

def ord_inv (i : Nat) (S : Set (Fin i → ℝ)) (f : MvPolynomial (Fin i) ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, polyOrder i f a = polyOrder i f b
