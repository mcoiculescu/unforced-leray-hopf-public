import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_3_1_3_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_3
import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: the time derivative of `u_k = J_k b`

Source of record: `the November 2 reference manuscript` (SP) lines 3427-3440 (the
equation `b_s + (μ/s) b - νΔb = 𝒫₀ div F` in the energy class on the cylinder) and 3541-3552 (the
energy identity). This file holds the concrete objects and the leaf statements of `LMDerivRepAE`
(`Sub/PartIIIa_T18_3_1_3_2_2.lean`).

## The Leray projection

The Leray projection of the cylinder is NOT missing: `Cyl.P0 c` (`Lib/CylinderB/Leray.lean`) is the
orthogonal projection of `L²(cell; ℝ²)` onto the closed subspace `Cyl.divFree c` of weakly
divergence-free fields (the orthogonal complement of the gradients of periodic tests), and
`P0C c f` (`Sub/T18_2_4_2.lean`) is its action on the real and imaginary parts of a `ℂ²`-valued
field. Everything below uses these. No Riesz representation is needed.

## The formula

Put `T = νG + F` (`lmTens`) and `Z(s) = ∑ⱼ ∂ⱼ J_k T(s)_{·j}` (`lmDivJ`). The weak derivative of
`u_k = J_k b` is
`u'(s) = -(μ/s) u_k(s) + 𝒫₀ Z(s)`,
the formula `-(μ/s) u_k + νΔu_k + J_k 𝒫₀ div F` of SP 3427-3440 with the viscous and force terms
written together. For `χ ∈ L²(cell; ℂ²)` the test `w = J_k 𝒫₀ χ` is a complexified `IsH1DivFreeTest`.
`ExtWeakH1` tested with `Re w`, `Im w` gives, for `ψ ∈ C_c^∞(0,∞)`,
`∫ (-ψ' ⟨w, b⟩ + ψ (μ/s) ⟨w, b⟩ + ψ ∑ᵢⱼ ∫ conj(∂ⱼ wᵢ) Tᵢⱼ) ds = 0` (`LMSliceTested`), and on a good
slice `⟨w, b⟩ = ⟨χ, u_k⟩` (self-adjointness of `J_k`, then `𝒫₀ u_k = u_k`) and
`∑ᵢⱼ ∫ conj(∂ⱼ wᵢ) Tᵢⱼ = -⟨χ, 𝒫₀ Z⟩` (`LMAntiSymm`, self-adjointness of `𝒫₀`).
Since this holds in integrated form for each `χ` there is no Lebesgue differentiation and no
separability of the test class in the argument.

## Two properties of the mollifier that `IsLMMollifier` does not state (`LMMollH1`)

* `gradL2`: `∂ⱼ J_k : L²(cell) → L²(cell)` is bounded for each fixed `k`. It cannot be derived from
  the clauses of `IsLMMollifier`, and `LMDerivRepAE` is false without it: those clauses are
  satisfied by a Fourier multiplier `m_k(ξ)` on the cylinder, `0 ≤ m_k ≤ 1`, `m_k → 1`,
  `ξ^α m_k ∈ L²` for every `α`, which equals `1` on thin spikes around a sequence `ξ_l → ∞` in the
  `η`-frequency (smooth output: `∫ |ξ^α m_k f̂| < ∞`; `ξ m_k` is unbounded). With shear data
  `b = (β(s, η), 0)` whose transform lives on the spikes and oscillates in `s` at frequency
  `ω_l ≫ ξ_l²`, one has `b, ∇b, F ∈ L²_loc` but `∂_s (J_k b) ∉ L²_loc((0,∞); L²)`, so no
  `LMWeakDeriv` exists. (A pen-and-paper construction, not formalised.) The actual mollifier `lmJ`
  has this bound by Young's inequality.
* `divFreeWeak`: `J_k` maps weakly divergence-free `L²` fields to classically divergence-free fields.
  The clause `IsLMMollifier.divFree` covers only smooth input, while `b(s)` is only weakly divergence
  free and `IsLMMollifier` does not say that `J_k` acts componentwise, so `commute` alone does not
  give it. The actual mollifier `lmJ` has it: `y ↦ K_k(x - y)` is a test, `LMPd j (lmJ f_j)(x) =
  -∫ f_j ∂ⱼ K_k(x - ·)`.

`LMDerivRepAEH1` is `LMDerivRepAE` with `LMMollH1 c J` as an added hypothesis. The follow-up organize
task `PartIII-a:T18/3/1/3/2/2/orgH1` adds the two clauses to `IsLMMollifier` itself, supplies them
for `lmJ`, and derives `LMDerivRepAE`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Objects -/

/-- Weakly divergence free on the cylinder, in the form of `IsCausalEnergySolution.divFree` and
`P0DivFreeC` (SP 3427-3440). -/
def LMWeakDivFree (c : ℝ) (f : LMSpField) : Prop :=
  ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
    ∫ x in B0579.cell c, (f x 0 * (B0579.pd 0 ψ x : ℂ) + f x 1 * (B0579.pd 1 ψ x : ℂ)) = 0

/-- The two properties of the mollifier used for the time derivative of `u_k = J_k b` (SP 3427-3440,
3541-3552); see the header of this file. -/
structure LMMollH1 (c : ℝ) (J : ℕ → LMSpField → LMSpField) : Prop where
  gradL2 : ∀ k : ℕ, ∃ C : ℝ, ∀ f : LMSpField, LMCellL2 c f → ∀ i j : Fin 2,
    MemLp (LMPd j (fun y => J k f y i)) 2 (volume.restrict (B0579.cell c)) ∧
      ∫ x in B0579.cell c, ‖LMPd j (fun y => J k f y i) x‖ ^ 2 ≤
        C * ∫ x in B0579.cell c, ∑ l : Fin 2, ‖f x l‖ ^ 2
  divFreeWeak : ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f → LMWeakDivFree c f →
    ∀ x : ℝ × ℝ, LMPd 0 (fun y => J k f y 0) x + LMPd 1 (fun y => J k f y 1) x = 0

/-- `T = νG + F`, the tensor of the equation in `ExtWeakH1` (SP 3427-3440). -/
def lmTens (ν : ℝ) (F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ :=
  fun p i j => (ν : ℂ) * G p i j + F p i j

/-- `Z = ∑ⱼ ∂ⱼ J_k T_{·j}`, the mollified divergence of a spatial tensor `T`. -/
def lmDivJ (J : ℕ → LMSpField → LMSpField) (k : ℕ) (T : ℝ × ℝ → Fin 2 → Fin 2 → ℂ) : LMSpField :=
  fun x i => ∑ j : Fin 2, LMPd j (fun y => J k (fun y' i' => T y' i' j) y i) x

/-- The candidate weak derivative `u'(s) = -(μ/s) u(s) + Y(s)`, where `Y(s) = 𝒫₀ Z(s)` a.e.
(SP 3427-3440). -/
def lmUDer (μ : ℂ) (u : ℝ → LMSpField) (Y : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) : ℝ → LMSpField :=
  fun s x i => -(μ / (s : ℂ)) * u s x i + Y (s, x) i

/-- `LMDerivRepAE` for mollifiers with the two properties of `LMMollH1` (SP 3427-3440, 3541-3552). -/
def LMDerivRepAEH1 : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → LMMollH1 c J →
    ExtWeakH1 c ν μ F b G → ∀ k : ℕ,
      ∃ u' : ℝ → LMSpField, LMWeakDeriv c (LMMollU J b k) u' ∧
        ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
          2 * (LMIp c (u' s) (LMMollU J b k s)).re =
            -(2 * μ.re / s * LMMollE c J b k s + 2 * ν * LMMollN c J b k s +
              2 * LMMollR c J F b k s)

/-! ## Elementary facts on the pairing `LMIp` (proved here) -/

theorem lmIp_integrable {c : ℝ} {f g : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g)
    (i : Fin 2) :
    Integrable (fun x => starRingEnd ℂ (f x i) * g x i) (volume.restrict (B0579.cell c)) :=
  ((hf i).star).integrable_mul (hg i)

theorem lmIp_add_right {c : ℝ} {f g h : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g)
    (hh : LMCellL2 c h) :
    LMIp c f (fun x i => g x i + h x i) = LMIp c f g + LMIp c f h := by
  unfold LMIp
  rw [← integral_add (integrable_finsetSum _ fun i _ => lmIp_integrable hf hg i)
    (integrable_finsetSum _ fun i _ => lmIp_integrable hf hh i)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [mul_add, Finset.sum_add_distrib]

theorem lmIp_add_left {c : ℝ} {f g h : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g)
    (hh : LMCellL2 c h) :
    LMIp c (fun x i => f x i + g x i) h = LMIp c f h + LMIp c g h := by
  unfold LMIp
  rw [← integral_add (integrable_finsetSum _ fun i _ => lmIp_integrable hf hh i)
    (integrable_finsetSum _ fun i _ => lmIp_integrable hg hh i)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_add, add_mul, Finset.sum_add_distrib]

theorem lmIp_smul_right (c : ℝ) (a : ℂ) (f g : LMSpField) :
    LMIp c f (fun x i => a * g x i) = a * LMIp c f g := by
  unfold LMIp
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show ∑ i, starRingEnd ℂ (f x i) * (a * g x i) = a * ∑ i, starRingEnd ℂ (f x i) * g x i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lmIp_smul_left (c : ℝ) (a : ℂ) (f g : LMSpField) :
    LMIp c (fun x i => a * f x i) g = starRingEnd ℂ a * LMIp c f g := by
  unfold LMIp
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show ∑ i, starRingEnd ℂ (a * f x i) * g x i = starRingEnd ℂ a * ∑ i, starRingEnd ℂ (f x i) * g x i
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring

theorem lmIp_congr_right {c : ℝ} {f g g' : LMSpField}
    (h : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i, g x i = g' x i) :
    LMIp c f g = LMIp c f g' := by
  unfold LMIp
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

theorem lmIp_congr_left {c : ℝ} {f f' g : LMSpField}
    (h : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i, f x i = f' x i) :
    LMIp c f g = LMIp c f' g := by
  unfold LMIp
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-- `⟨f, g⟩` and `⟨g, f⟩` are conjugate. -/
theorem lmIp_conj (c : ℝ) (f g : LMSpField) :
    starRingEnd ℂ (LMIp c f g) = LMIp c g f := by
  unfold LMIp
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show starRingEnd ℂ (∑ i, starRingEnd ℂ (f x i) * g x i) = ∑ i, starRingEnd ℂ (g x i) * f x i
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, Complex.conj_conj]; ring

/-- The self pairing is the squared norm, written with `vnorm2`. -/
theorem lmIp_self (c : ℝ) (f : LMSpField) :
    LMIp c f f = ((∫ x in B0579.cell c, vnorm2 (f x) ^ 2 : ℝ) : ℂ) := by
  unfold LMIp
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have h : vnorm2 (f x) ^ 2 = ∑ i : Fin 2, ‖f x i‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  simp only [h]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- The slice `T(s)_{·j}` of `T = νG + F` is in `L²(cell)` on a good slice. -/
theorem lmTens_col_cellL2 {c ν : ℝ} {F G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ} {s : ℝ} (h : LMGoodSlice c F G b s) (j : Fin 2) :
    LMCellL2 c (fun y i => lmTens ν F G (s, y) i j) := fun i =>
  ((h.2.1 j i).const_mul _).add (h.2.2 j i)

/-- `Z` is in `L²(cell)` when the columns of `T` are. -/
theorem lmDivJ_cellL2 {c : ℝ} {J : ℕ → LMSpField → LMSpField} (hX : LMMollH1 c J) (k : ℕ)
    {T : ℝ × ℝ → Fin 2 → Fin 2 → ℂ} (hT : ∀ j, LMCellL2 c (fun y i => T y i j)) :
    LMCellL2 c (lmDivJ J k T) := by
  obtain ⟨C, hC⟩ := hX.gradL2 k
  intro i
  unfold lmDivJ
  exact memLp_finsetSum _ fun j _ => (hC _ (hT j) i j).1

/-- `𝒫₀ f` is in `L²(cell)` for every field `f`. -/
theorem lmP0C_cellL2 (c : ℝ) (f : LMSpField) : LMCellL2 c (P0C c f) := by
  intro i
  rw [← cellμ_eq c]
  have h1 := UnforcedLeray.Cyl.memLp_component (P0re c f) i
  have h2 := UnforcedLeray.Cyl.memLp_component (P0im c f) i
  have h := h1.ofReal (K := ℂ) |>.add (h2.ofReal (K := ℂ) |>.const_mul Complex.I)
  exact h

end UnforcedLeray.Short.IIIa
