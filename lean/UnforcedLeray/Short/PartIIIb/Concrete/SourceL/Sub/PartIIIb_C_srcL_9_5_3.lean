import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6

/-!
# Decomposition of `scChiJet` (source 4161-4166, 4178-4186)

`SCChiJet χy` from: smoothness of `cylR` off the axis, the one-variable jets of `χ_y(ν/r²)` and
`χ_y'(r)/r`-type factor (`SCChi1D`), and the composition bound with `cylR` (`SCCylComp`,
Faà di Bruno via `norm_iteratedFDeriv_comp_le` and `D^j cylR ≲ r^{1-j}`).
Source: `the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `cylR = √(y₀²+y₁²)` is smooth off the axis (4178-4186). -/
def SCCylRSmooth : Prop :=
  ∀ y : Vec3, 0 < cylR y → ContDiffAt ℝ 7 cylR y

/-- One-variable jets of the cutoff (4161-4166, 4178-4186): with `φ = chiYr ν 1 χy`,
`φ(r) = χy(ν/r²)` is `0` for `r² < ν`, and for `r² ≥ ν` every `φ^{(k)}(r)` is a combination
`Σ a_{k,i}(ν/r²)^i χy^{(i)}(ν/r²) r^{-k}` with `ν/r²∈[0,1]`, so `|φ^{(k)}(r)| ≤ C r^{-k}`; likewise
`|(φ'/r)^{(k)}(r)| ≤ C r^{-2-k}`; `C` depends only on `χy` (not on `ν`); `k ≤ 7`, `r > 0`. -/
def SCChi1D (χy : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ ν : ℝ, 0 < ν → IsStreamCutoff χy → ∀ k : ℕ, k ≤ 7 → ∀ r : ℝ, 0 < r →
    |iteratedDeriv k (chiYr ν 1 χy) r| ≤ C * r ^ (-(k : ℝ)) ∧
    |iteratedDeriv k (fun r => deriv (chiYr ν 1 χy) r / r) r| ≤ C * r ^ (-(2 : ℝ) - k)

/-- Composition with `cylR` (Faà di Bruno; `‖D^j cylR(y)‖ ≤ C_j r^{1-j}`, `j ≤ 7`, `r = cylR y > 0`,
via `norm_iteratedFDeriv_comp_le`): there is an absolute `C0` such that if `f` is `C^7` on `(0,∞)`
with `|f^{(k)}(r)| ≤ A r^{-p-k}` (`k ≤ 7`, `r>0`, `0 ≤ p`, `p ≤ 2`) then
`‖D^m (f∘cylR)(y)‖ ≤ C0 A r^{-p-m}` for `m ≤ 7`. -/
def SCCylComp : Prop :=
  ∃ C0 : ℝ, ∀ (p A : ℝ) (f : ℝ → ℝ), 0 ≤ p → p ≤ 2 → 0 ≤ A → ContDiffOn ℝ 7 f (Ioi 0) →
    (∀ k : ℕ, k ≤ 7 → ∀ r : ℝ, 0 < r → |iteratedDeriv k f r| ≤ A * r ^ (-p - k)) →
    ∀ m : ℕ, m ≤ 7 → ∀ y : Vec3, 0 < cylR y →
      ‖iteratedFDeriv ℝ m (fun y => f (cylR y)) y‖ ≤ C0 * A * cylR y ^ (-p - m)

theorem scChiJet_of {χy : ℝ → ℝ} (hR : SCCylRSmooth) (h1 : SCChi1D χy) (hC : SCCylComp) :
    SCChiJet χy := by
  obtain ⟨C, hCb⟩ := h1
  obtain ⟨C0, hC0⟩ := hC
  refine ⟨|C0| * |C|, ?_⟩
  intro ν hν hχ y hy
  have hmem : cylR y ∈ Ioi (0 : ℝ) := hy
  have hφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chiYr ν 1 χy) (Ioi 0) :=
    chiYr_contDiffOn hχ one_pos
  have hdφ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (chiYr ν 1 χy)) (Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hφ).2
  have hψ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r => deriv (chiYr ν 1 χy) r / r) (Ioi 0) :=
    hdφ.div contDiffOn_id (fun r hr => ne_of_gt hr)
  have h7 : ((7 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    have : (((7 : ℕ∞)) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    simpa using this
  have hφ7 : ContDiffOn ℝ 7 (chiYr ν 1 χy) (Ioi 0) := by
    exact hφ.of_le h7
  have hψ7 : ContDiffOn ℝ 7 (fun r => deriv (chiYr ν 1 χy) r / r) (Ioi 0) := by
    exact hψ.of_le h7
  have hcy : ContDiffAt ℝ 7 cylR y := hR y hy
  have hat1 : ContDiffAt ℝ 7 (chiYr ν 1 χy) (cylR y) :=
    hφ7.contDiffAt (isOpen_Ioi.mem_nhds hmem)
  have hat2 : ContDiffAt ℝ 7 (fun r => deriv (chiYr ν 1 χy) r / r) (cylR y) :=
    hψ7.contDiffAt (isOpen_Ioi.mem_nhds hmem)
  have hb : ∀ k : ℕ, k ≤ 7 → ∀ r : ℝ, 0 < r →
      |iteratedDeriv k (chiYr ν 1 χy) r| ≤ |C| * r ^ (-(0 : ℝ) - k) ∧
      |iteratedDeriv k (fun r => deriv (chiYr ν 1 χy) r / r) r| ≤ |C| * r ^ (-(2 : ℝ) - k) := by
    intro k hk r hr
    obtain ⟨a, b⟩ := hCb ν hν hχ k hk r hr
    have p1 : 0 ≤ r ^ (-(0 : ℝ) - k) := Real.rpow_nonneg hr.le _
    have p2 : 0 ≤ r ^ (-(2 : ℝ) - k) := Real.rpow_nonneg hr.le _
    refine ⟨?_, ?_⟩
    · rw [neg_zero, zero_sub]
      exact a.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hr.le _))
    · exact b.trans (mul_le_mul_of_nonneg_right (le_abs_self _) p2)
  refine ⟨hat1.comp y hcy, hat2.comp y hcy, fun m hm => ⟨?_, ?_⟩⟩
  · have := hC0 0 |C| (chiYr ν 1 χy) le_rfl (by norm_num) (abs_nonneg _) hφ7
      (fun k hk r hr => (hb k hk r hr).1) m hm y hy
    have e : (-(0 : ℝ) - m) = -(m : ℝ) := by ring
    rw [e] at this
    have hp : 0 ≤ cylR y ^ (-(m : ℝ)) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    exact this.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)) hp)
  · exact (hC0 2 |C| _ (by norm_num) le_rfl (abs_nonneg _) hψ7
      (fun k hk r hr => (hb k hk r hr).2) m hm y hy).trans (by
      have hp : 0 ≤ cylR y ^ (-(2 : ℝ) - m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)) hp)

end UnforcedLeray.Short.PartIIIb.Concrete
