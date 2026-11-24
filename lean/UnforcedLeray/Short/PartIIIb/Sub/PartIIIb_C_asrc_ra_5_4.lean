import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.Targets
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.PerGen
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.AffineLiftReg.FEPer

/-!
# `PartIII-b:C/asrc/ra/5/4` and `/6` : term-level reduction for `affFECont` and `psipAC3`

Source of record: `the November 2 reference manuscript` lines 4963-4981, 4978
("The sums and their required derivatives converge by Gaussian decay").

The lattice sums `fA`, `eA`, `psipA` are `∑' j, G(s, (q - j c, η))` with `G` the `j = 0` term
(translation identities below).  The regularity of the sums on `s > 0` therefore follows from
`contDiffOn_tsum_shift` once the `j = 0` term is `C^n` on `Ioi 0 ×ˢ univ` and has Gaussian-in-`q`
derivative bounds, locally uniform in `s` and `η`.  Those two facts are the Props
`PsipTermReg`, `FTermReg`, `ETermReg` (source 4963-4975, 4978); this file proves the reduction
`psipAC3_of`, `affFECont_of`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Gaussian-in-`q` derivative bounds, locally uniform in `s` and `η` (the hypothesis `hbd` of
`contDiffOn_tsum_shift` with `U = Ioi 0`). -/
def TermBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (G : ℝ × (ℝ × ℝ) → E) : Prop :=
  ∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K → ∀ L : Set ℝ, IsCompact L →
    ∃ C a : ℝ, 0 < a ∧ ∀ m : ℕ, m ≤ n → ∀ s ∈ K, ∀ q : ℝ, ∀ η ∈ L,
      ‖iteratedFDeriv ℝ m G (s, (q, η))‖ ≤ C * Real.exp (-a * q ^ 2)

/-- The `j = 0` term of `ψ^p_A` is `C³` on `s > 0` with Gaussian bounds (source 4974-4975, 4978;
`A` is `C⁶`, `ψ_0 = -2 a⁻¹ e^{-|x|²/(4a)}`). -/
def PsipTermReg (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => psipATerm ν χf A p.1 p.2 0)
        (Ioi (0 : ℝ) ×ˢ univ) ∧
      TermBound 3 (fun p : ℝ × (ℝ × ℝ) => psipATerm ν χf A p.1 p.2 0)

/-- The `j = 0` term of `-f_A` is continuous on `s > 0` with Gaussian bounds (source 4970, 4978;
involves `B = (A^y)' + μ A^y / s`, `V_0`, `DV_0`). -/
def FTermReg (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => fATerm ν μ χf A p.1 p.2 0)
        (Ioi (0 : ℝ) ×ˢ univ) ∧
      TermBound 0 (fun p : ℝ × (ℝ × ℝ) => fATerm ν μ χf A p.1 p.2 0)

/-- The `j = 0` term of `e_A` is continuous on `s > 0` with Gaussian bounds (source 4971-4972,
4978; involves `B`, `A^y`, `V_0`, `D²V_0`, `∇p_0`). -/
def ETermReg (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν μ : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => eATerm ν μ χf A p.1 p.2 0)
        (Ioi (0 : ℝ) ×ˢ univ) ∧
      TermBound 0 (fun p : ℝ × (ℝ × ℝ) => eATerm ν μ χf A p.1 p.2 0)

/-! ## Machinery classes for the term-level lemmas (used by the lemma tasks) -/

/-- `GP54 κ ν n f` : `f(s, x)` is `C^n` on `s > 0` and its derivatives of order `≤ n` are bounded,
locally uniformly in `s ∈ [s₀, s₁]`, by `C (1 + |x|²)^N exp(-|x|²/(κ a(s₁)))`, `a = 1 + νs`
(the shape produced by `gauss_iterated_bound`, source 4963-4968, 4978). -/
def GP54 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ ν : ℝ) (n : ℕ)
    (f : ℝ × (ℝ × ℝ) → E) : Prop :=
  ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) f (Ioi (0 : ℝ) ×ˢ univ) ∧
    ∀ s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ m : ℕ, m ≤ n →
      ∀ s ∈ Icc s0 s1, ∀ x : ℝ × ℝ,
        ‖iteratedFDeriv ℝ m f (s, x)‖ ≤
          C * (1 + sq2 x) ^ N * Real.exp (-(sq2 x) / (κ * ageA ν s1))

/-- `PS54 n g` : `g(s, x)` is `C^n` on `s > 0` and its derivatives of order `≤ n` have polynomial
growth in `x`, locally uniformly in `s ∈ [s₀, s₁]`. -/
def PS54 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (g : ℝ × (ℝ × ℝ) → E) : Prop :=
  ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) g (Ioi (0 : ℝ) ×ˢ univ) ∧
    ∀ s0 s1 : ℝ, 0 < s0 → s0 ≤ s1 → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ m : ℕ, m ≤ n →
      ∀ s ∈ Icc s0 s1, ∀ x : ℝ × ℝ,
        ‖iteratedFDeriv ℝ m g (s, x)‖ ≤ C * (1 + sq2 x) ^ N

/-! ## Translation identities: term `j` at `x` is term `0` at `x_j` -/

theorem cOf_pos' {ν : ℝ} (hν : 0 < ν) : 0 < cOf ν := by
  unfold cOf; positivity

theorem xj_zero (ν : ℝ) (y : ℝ × ℝ) : xj ν 0 y = y := by
  unfold xj; ext <;> simp

theorem pt_shift (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    x = ((xj ν j x).1 + (j : ℝ) * cOf ν, (xj ν j x).2) := by
  unfold xj; ext <;> simp

theorem psij_shift_zero (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    psij ν s j x = psij ν s 0 (xj ν j x) := by
  have h := hper_psij_shift ν s j j (xj ν j x)
  rw [← pt_shift] at h
  rw [h]; simp

theorem fderiv_psij_shift_zero (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    fderiv ℝ (psij ν s j) x = fderiv ℝ (psij ν s 0) (xj ν j x) := by
  have h := hper_fderiv_shift (psij ν s j) (psij ν s 0) ((j : ℝ) * cOf ν)
    (fun y => by rw [hper_psij_shift]; simp) (xj ν j x)
  rw [← pt_shift] at h
  exact h

theorem Vj_shift_zero (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    Vj ν s j x = Vj ν s 0 (xj ν j x) := by
  have h := hper_Vj_shift ν s j j (xj ν j x)
  rw [← pt_shift] at h
  rw [h]; simp

theorem fderiv_Vj_shift_zero (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) x = fderiv ℝ (Vj ν s 0) (xj ν j x) := by
  have h := hper_fderiv_shift (Vj ν s j) (Vj ν s 0) ((j : ℝ) * cOf ν)
    (fun y => by rw [hper_Vj_shift]; simp) (xj ν j x)
  rw [← pt_shift] at h
  exact h

theorem hess_shift_zero (ν s : ℝ) (A : Mat3) (j : ℤ) (x : ℝ × ℝ) :
    hessContr A (Vj ν s j) x = hessContr A (Vj ν s 0) (xj ν j x) := by
  have h := fe_hess ν s A j j (xj ν j x)
  rw [← pt_shift] at h
  rw [h]; simp

theorem mgrad_shift_zero (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) :
    mgrad (pj ν s j) x = mgrad (pj ν s 0) (xj ν j x) := by
  have h := fe_mgrad ν s j j (xj ν j x)
  rw [← pt_shift] at h
  rw [h]; simp

theorem psipATerm_shift (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) :
    psipATerm ν χ A s x j = psipATerm ν χ A s (xj ν j x) 0 := by
  unfold psipATerm
  rw [psij_shift_zero ν s j x, fderiv_psij_shift_zero ν s j x, xj_zero ν (xj ν j x)]

theorem fATerm_shift (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) :
    fATerm ν μ χ A s x j = fATerm ν μ χ A s (xj ν j x) 0 := by
  unfold fATerm
  rw [Vj_shift_zero ν s j x, fderiv_Vj_shift_zero ν s j x, xj_zero ν (xj ν j x)]

theorem eATerm_shift (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) :
    eATerm ν μ χ A s x j = eATerm ν μ χ A s (xj ν j x) 0 := by
  unfold eATerm
  rw [Vj_shift_zero ν s j x, hess_shift_zero ν s _ j x, mgrad_shift_zero ν s j x]

/-! ## The reductions -/

theorem psipAC3_of (as : ℝ) (χf : ℝ → ℝ) (h : PsipTermReg as χf) : PsipAC3 as χf := by
  intro hχ ν hν A hA
  obtain ⟨hG, hb⟩ := h hχ ν hν A hA
  have key := contDiffOn_tsum_shift 3 (cOf ν) (cOf_pos' hν) (Ioi (0 : ℝ)) isOpen_Ioi _ hG hb
  have key' : ContDiffOn ℝ ((3 : ℕ) : WithTop ℕ∞) (fun p : ℝ × (ℝ × ℝ) => psipA ν χf A p.1 p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
    refine key.congr (fun p _ => ?_)
    rw [psipA_eq]
    exact tsum_congr (fun j => psipATerm_shift ν χf A p.1 p.2 j)
  exact_mod_cast key'

theorem merOf_continuous : Continuous merOf := by
  unfold merOf
  fun_prop

theorem affFECont_of (as : ℝ) (χf : ℝ → ℝ) (hF : FTermReg as χf) (hE : ETermReg as χf) :
    AffFECont as χf := by
  intro hχ ν μ hν A hA
  obtain ⟨hG, hb⟩ := hF hχ ν μ hν A hA
  obtain ⟨hG', hb'⟩ := hE hχ ν μ hν A hA
  have kF := contDiffOn_tsum_shift 0 (cOf ν) (cOf_pos' hν) (Ioi (0 : ℝ)) isOpen_Ioi _ hG hb
  have kE := contDiffOn_tsum_shift 0 (cOf ν) (cOf_pos' hν) (Ioi (0 : ℝ)) isOpen_Ioi _ hG' hb'
  have cF : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => fA ν μ χf A p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ) := by
    have : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ∑' j : ℤ, fATerm ν μ χf A p.1 (p.2.1 - j * cOf ν, p.2.2) 0)
        (Ioi (0 : ℝ) ×ˢ univ) := kF.continuousOn
    have := this.neg
    refine this.congr (fun p _ => ?_)
    rw [fA_eq]
    simp only [Pi.neg_apply]
    congr 1
    exact tsum_congr (fun j => fATerm_shift ν μ χf A p.1 p.2 j)
  have cE : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => eA ν μ χf A p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ) := by
    have : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ∑' j : ℤ, eATerm ν μ χf A p.1 (p.2.1 - j * cOf ν, p.2.2) 0)
        (Ioi (0 : ℝ) ×ˢ univ) := kE.continuousOn
    refine this.congr (fun p _ => ?_)
    rw [eA_eq]
    exact tsum_congr (fun j => eATerm_shift ν μ χf A p.1 p.2 j)
  have hs : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => p.1) (Ioi (0 : ℝ) ×ˢ univ) := continuousOn_fst
  have hs0 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)), p.1 ≠ 0 := fun p hp => ne_of_gt hp.1
  have h1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => (Real.sqrt p.1)⁻¹) (Ioi (0 : ℝ) ×ˢ univ) :=
    (hs.sqrt).inv₀ (fun p hp => (Real.sqrt_pos.2 hp.1).ne')
  have h2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => p.1 ^ (3 / 2 : ℝ)) (Ioi (0 : ℝ) ×ˢ univ) :=
    hs.rpow_const (fun p hp => Or.inl (hs0 p hp))
  have hmer : ∀ (g : ℝ × (ℝ × ℝ) → Vec3), ContinuousOn g (Ioi (0 : ℝ) ×ˢ univ) →
      ContinuousOn (fun p => merOf (g p)) (Ioi (0 : ℝ) ×ˢ univ) :=
    fun g hg => merOf_continuous.comp_continuousOn hg
  have hA' : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • fA ν μ χf A p.1 p.2))) (Ioi (0 : ℝ) ×ˢ univ) :=
    hmer _ (h1.smul (h2.smul cF))
  have hB' : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => merOf ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • eA ν μ χf A p.1 p.2))) (Ioi (0 : ℝ) ×ˢ univ) :=
    hmer _ (h1.smul (h2.smul cE))
  exact hA'.add hB'

end UnforcedLeray.Short.PartIIIb.Concrete
