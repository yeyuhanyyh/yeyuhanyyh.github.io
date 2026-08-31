import GDLowerBound.FiniteConvexProjection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The original orthogonal support-envelope chain
-/

namespace GDLowerBound

noncomputable section

open scoped BigOperators InnerProductSpace
open Set Real

/-- Positive block scales for one selected subsequence. -/
structure ChainData (m : ℕ) where
  U : Fin m → ℝ
  y : Fin m → ℝ
  terminal : ℝ
  U_pos : ∀ i, 0 < U i
  y_pos : ∀ i, 0 < y i
  terminal_pos : 0 < terminal

namespace ChainData

variable {m : ℕ} (d : ChainData m)

abbrev Space := EuclideanSpace ℝ (Fin (m + 1))

/-- Standard orthonormal coordinate vector. -/
def e (i : Fin (m + 1)) : d.Space := EuclideanSpace.single i 1

lemma orthonormal_e : Orthonormal ℝ d.e := EuclideanSpace.orthonormal_single

lemma inner_e (i j : Fin (m + 1)) :
    inner ℝ (d.e i) (d.e j) = if i = j then 1 else 0 :=
  (orthonormal_iff_ite.mp d.orthonormal_e) i j

/-- Block scale, with the terminal block at index `m`. -/
def H (i : Fin (m + 1)) : ℝ :=
  if h : i.1 < m then d.U ⟨i.1, h⟩ + d.y ⟨i.1, h⟩ else d.terminal

@[simp] lemma H_castSucc (i : Fin m) : d.H i.castSucc = d.U i + d.y i := by
  simp [H, i.isLt]

@[simp] lemma H_last : d.H (Fin.last m) = d.terminal := by
  simp [H]

lemma H_pos (i : Fin (m + 1)) : 0 < d.H i := by
  by_cases h : i.1 < m
  · simp [H, h, d.U_pos ⟨i.1, h⟩, d.y_pos ⟨i.1, h⟩]
  · simp [H, h, d.terminal_pos]

/-- The local contraction factor `χ_i`. -/
def chi (i : Fin m) : ℝ :=
  d.y i * d.H i.succ /
    (d.U i * (d.H i.castSucc + d.H i.succ))

lemma chi_pos (i : Fin m) : 0 < d.chi i := by
  unfold chi
  positivity

/-- Square-root contraction factor. -/
def gamma (i : Fin m) : ℝ := Real.sqrt (d.chi i)

lemma gamma_pos (i : Fin m) : 0 < d.gamma i := Real.sqrt_pos.2 (d.chi_pos i)

lemma gamma_sq (i : Fin m) : d.gamma i ^ 2 = d.chi i := by
  rw [gamma, sq_sqrt]
  exact (d.chi_pos i).le

/-- A natural-number extension used to define prefix products. -/
def gammaNat (j : ℕ) : ℝ := if h : j < m then d.gamma ⟨j, h⟩ else 1

/-- Anchor length `ℓ_i = ∏_{j<i} γ_j`. -/
def ell (i : Fin (m + 1)) : ℝ := ∏ j ∈ Finset.range i.1, d.gammaNat j

@[simp] lemma ell_zero : d.ell ⟨0, Nat.zero_lt_succ m⟩ = 1 := by simp [ell]

lemma ell_succ (i : Fin m) : d.ell i.succ = d.ell i.castSucc * d.gamma i := by
  rw [ell, ell, Finset.prod_range_succ]
  simp [gammaNat, i.isLt]

lemma ell_pos (i : Fin (m + 1)) : 0 < d.ell i := by
  unfold ell
  apply Finset.prod_pos
  intro j hj
  have hjm : j < m := by
    have hji : j < i.1 := Finset.mem_range.mp hj
    omega
  simp [gammaNat, hjm, d.gamma_pos ⟨j, hjm⟩]

/-- Orthogonal anchor `X_i=ℓ_i e_i`. -/
def anchor (i : Fin (m + 1)) : d.Space := d.ell i • d.e i

/-- Gradient vertex at a block or at the terminal coordinate. -/
def grad (i : Fin (m + 1)) : d.Space :=
  if h : i.1 < m then
    let j : Fin m := ⟨i.1, h⟩
    (d.ell i / d.H i) • (d.e i - d.gamma j • d.e j.succ)
  else
    (d.ell i / d.H i) • d.e i

@[simp] lemma grad_castSucc (i : Fin m) :
    d.grad i.castSucc =
      (d.ell i.castSucc / d.H i.castSucc) •
        (d.e i.castSucc - d.gamma i • d.e i.succ) := by
  simp [grad, i.isLt]

@[simp] lemma grad_last :
    d.grad (Fin.last m) =
      (d.ell (Fin.last m) / d.H (Fin.last m)) • d.e (Fin.last m) := by
  simp [grad]

/-- Generator set `conv {0,g_0,...,g_m}`. -/
def vertices : Finset d.Space := insert 0 (Finset.univ.image d.grad)

lemma zero_mem_vertices : (0 : d.Space) ∈ d.vertices := by simp [vertices]

lemma grad_mem_vertices (i : Fin (m + 1)) : d.grad i ∈ d.vertices := by
  simp [vertices]

/-- The compact convex gradient set used by the hard instance. -/
def convexSet : FiniteConvexSet d.Space where
  vertices := d.vertices
  zero_mem := d.zero_mem_vertices

lemma grad_mem_carrier (i : Fin (m + 1)) : d.grad i ∈ d.convexSet.carrier :=
  subset_convexHull ℝ (d.vertices : Set d.Space) (d.grad_mem_vertices i)

/-- Point after cumulative mass `s` inside block `i`. -/
def blockPoint (i : Fin m) (s : ℝ) : d.Space :=
  d.anchor i.castSucc - s • d.grad i.castSucc

/-- Residual vector `q_i(u-1)-g_i`. -/
def blockResidual (i : Fin m) (u : ℝ) : d.Space :=
  d.blockPoint i (u - 1) - d.grad i.castSucc

lemma blockResidual_eq (i : Fin m) (u : ℝ) :
    d.blockResidual i u =
      (d.ell i.castSucc / d.H i.castSucc) •
        ((d.H i.castSucc - u) • d.e i.castSucc +
          (u * d.gamma i) • d.e i.succ) := by
  simp only [blockResidual, blockPoint, anchor, grad_castSucc]
  module
  ring

lemma inner_grad_self_residual (i : Fin m) (u : ℝ) :
    inner ℝ (d.grad i.castSucc) (d.blockResidual i u) =
      d.ell i.castSucc ^ 2 / d.H i.castSucc ^ 2 *
        (d.H i.castSucc - u * (1 + d.gamma i ^ 2)) := by
  rw [d.blockResidual_eq]
  simp only [grad_castSucc, inner_smul_left, inner_smul_right, map_div₀,
    map_ofNat, map_one, starRingEnd_apply, star_trivial, inner_sub_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [d.inner_e i.castSucc i.castSucc, d.inner_e i.castSucc i.succ,
    d.inner_e i.succ i.castSucc, d.inner_e i.succ i.succ]
  simp
  ring

end ChainData

end

end GDLowerBound
