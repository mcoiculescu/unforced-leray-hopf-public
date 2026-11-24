import UnforcedLeray.Lib.Gaussian
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Helper for `PartI:T08/1/2`: Gaussian times polynomial on the plane is Schwartz

The Gaussian `exp (-b (z.1² + z.2²))` is a Schwartz function on `ℝ × ℝ` (pull back of the heat
kernel on `Euc 2`, whose iterated derivatives are bounded by `norm_iteratedFDeriv_gaussKernel_le`),
and the Schwartz functions are closed under multiplication by the coordinates and by each other.
-/

set_option autoImplicit false

noncomputable section

open scoped SchwartzMap ContDiff

namespace UnforcedLeray.Short.PartI.QcSmoothAux

open UnforcedLeray.Gaussian

/-- The heat kernel on `Euc 2` as a Schwartz function. -/
def gaussEuc {t : ℝ} (ht : 0 < t) : 𝓢(Euc 2, ℝ) where
  toFun := gaussKernel 2 t
  smooth' := contDiff_gaussKernel t
  decay' := by
    intro k n
    obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_gaussKernel_le 2 n
    obtain ⟨M, hM0, hM⟩ := rpow_mul_exp_neg_mul_sq_le (m := (k : ℝ)) (b := 1 / (8 * t))
      (Nat.cast_nonneg k) (by positivity)
    refine ⟨C * t ^ (-((((2 : ℕ) : ℝ) + n) / 2)) * M, fun x => ?_⟩
    have h1 := hC ht x
    have h2 := hM ‖x‖ (norm_nonneg _)
    rw [Real.rpow_natCast] at h2
    have e : Real.exp (-‖x‖ ^ 2 / (8 * t)) = Real.exp (-(1 / (8 * t) * ‖x‖ ^ 2)) := by
      congr 1; field_simp
    rw [e] at h1
    have hpos : 0 ≤ C * t ^ (-((((2 : ℕ) : ℝ) + n) / 2)) := by positivity
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (gaussKernel 2 t) x‖
        ≤ ‖x‖ ^ k * (C * t ^ (-((((2 : ℕ) : ℝ) + n) / 2)) * Real.exp (-(1 / (8 * t) * ‖x‖ ^ 2))) := by
          gcongr
      _ = (C * t ^ (-((((2 : ℕ) : ℝ) + n) / 2))) *
            (‖x‖ ^ k * Real.exp (-(1 / (8 * t) * ‖x‖ ^ 2))) := by ring
      _ ≤ _ := by gcongr


/-- The coordinate embedding `ℝ × ℝ → Euc 2`. -/
def embed : (ℝ × ℝ) →L[ℝ] Euc 2 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

theorem norm_embed_sq (z : ℝ × ℝ) : ‖embed z‖ ^ 2 = z.1 ^ 2 + z.2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [embed, Fin.sum_univ_two]

theorem norm_le_embed (z : ℝ × ℝ) : ‖z‖ ≤ ‖embed z‖ := by
  have h : ‖z‖ ^ 2 ≤ ‖embed z‖ ^ 2 := by
    rw [norm_embed_sq]
    have h1 : ‖z‖ = max |z.1| |z.2| := by
      rw [Prod.norm_def]; rfl
    rcases max_choice |z.1| |z.2| with h | h <;> rw [h1, h]
    · nlinarith [sq_abs z.1, sq_nonneg z.2]
    · nlinarith [sq_abs z.2, sq_nonneg z.1]
  exact le_of_sq_le_sq h (norm_nonneg _) |>.trans_eq rfl

/-- `exp (-b (x² + y²))` as a Schwartz function on the plane. -/
def gaussPlane {b : ℝ} (hb : 0 < b) : 𝓢(ℝ × ℝ, ℝ) :=
  (4 * Real.pi * (1 / (4 * b))) •
    SchwartzMap.compCLM ℝ (F := ℝ) embed.hasTemperateGrowth
      ⟨1, 1, fun x => by
        simp only [pow_one, one_mul]; linarith [norm_le_embed x]⟩ (gaussEuc (t := 1 / (4 * b)) (by positivity))

theorem gaussPlane_apply {b : ℝ} (hb : 0 < b) (z : ℝ × ℝ) :
    gaussPlane hb z = Real.exp (-(b * (z.1 ^ 2 + z.2 ^ 2))) := by
  have e1 : (gaussPlane hb) z = (4 * Real.pi * (1 / (4 * b))) *
      gaussKernel 2 (1 / (4 * b)) (embed z) := rfl
  rw [e1, gaussKernel, norm_embed_sq]
  have hpi : (0 : ℝ) < 4 * Real.pi * (1 / (4 * b)) := by positivity
  have : (4 * Real.pi * (1 / (4 * b))) ^ (-((2 : ℕ) : ℝ) / 2) = (4 * Real.pi * (1 / (4 * b)))⁻¹ := by
    rw [show (-((2 : ℕ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  rw [this]
  have e : -(z.1 ^ 2 + z.2 ^ 2) / (4 * (1 / (4 * b))) = -(b * (z.1 ^ 2 + z.2 ^ 2)) := by
    field_simp
  rw [e]
  field_simp

/-- The Schwartz functions on the plane (as plain functions). -/
def SchFn (f : ℝ × ℝ → ℝ) : Prop := ∃ s : 𝓢(ℝ × ℝ, ℝ), ⇑s = f

theorem SchFn.gauss {b : ℝ} (hb : 0 < b) :
    SchFn (fun z : ℝ × ℝ => Real.exp (-(b * (z.1 ^ 2 + z.2 ^ 2)))) :=
  ⟨gaussPlane hb, funext (gaussPlane_apply hb)⟩

theorem SchFn.mul_fst {f : ℝ × ℝ → ℝ} (h : SchFn f) : SchFn (fun z => z.1 * f z) := by
  obtain ⟨s, rfl⟩ := h
  have hg : (fun z : ℝ × ℝ => z.1).HasTemperateGrowth :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth
  exact ⟨SchwartzMap.smulLeftCLM ℝ (fun z : ℝ × ℝ => z.1) s, by
    rw [SchwartzMap.smulLeftCLM_apply hg]; rfl⟩

theorem SchFn.mul_snd {f : ℝ × ℝ → ℝ} (h : SchFn f) : SchFn (fun z => z.2 * f z) := by
  obtain ⟨s, rfl⟩ := h
  have hg : (fun z : ℝ × ℝ => z.2).HasTemperateGrowth :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  exact ⟨SchwartzMap.smulLeftCLM ℝ (fun z : ℝ × ℝ => z.2) s, by
    rw [SchwartzMap.smulLeftCLM_apply hg]; rfl⟩

theorem SchFn.const_mul {f : ℝ × ℝ → ℝ} (h : SchFn f) (c : ℝ) : SchFn (fun z => c * f z) := by
  obtain ⟨s, rfl⟩ := h
  exact ⟨c • s, rfl⟩

theorem SchFn.mul {f g : ℝ × ℝ → ℝ} (hf : SchFn f) (hg : SchFn g) : SchFn (fun z => f z * g z) := by
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨t, rfl⟩ := hg
  exact ⟨SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) t.hasTemperateGrowth s, rfl⟩

theorem SchFn.contDiff {f : ℝ × ℝ → ℝ} (h : SchFn f) : ContDiff ℝ ∞ f := by
  obtain ⟨s, rfl⟩ := h
  exact s.smooth ⊤

/-- Derivative decay of a Schwartz function in the form needed for periodization. -/
theorem SchFn.decay {f : ℝ × ℝ → ℝ} (h : SchFn f) (n : ℕ) :
    ∃ C : ℝ, ∀ z : ℝ × ℝ, ‖iteratedFDeriv ℝ n f z‖ ≤ C * (1 + |z.1|) ^ (-(2 : ℝ)) := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨C0, _, h0⟩ := s.decay 0 n
  obtain ⟨C2, _, h2⟩ := s.decay 2 n
  refine ⟨2 * (C0 + C2), fun z => ?_⟩
  have a0 := h0 z
  have a2 := h2 z
  have hn : 0 ≤ ‖iteratedFDeriv ℝ n s z‖ := norm_nonneg _
  have hz : |z.1| ≤ ‖z‖ := by simpa using norm_fst_le z
  have hpos : 0 < (1 + |z.1|) ^ 2 := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ hpos]
  have : (1 + |z.1|) ^ 2 ≤ 2 * (1 + ‖z‖ ^ 2) := by nlinarith [abs_nonneg z.1, sq_nonneg (|z.1| - 1)]
  calc ‖iteratedFDeriv ℝ n s z‖ * (1 + |z.1|) ^ 2
      ≤ ‖iteratedFDeriv ℝ n s z‖ * (2 * (1 + ‖z‖ ^ 2)) := by gcongr
    _ = 2 * (‖z‖ ^ 0 * ‖iteratedFDeriv ℝ n s z‖ + ‖z‖ ^ 2 * ‖iteratedFDeriv ℝ n s z‖) := by ring
    _ ≤ 2 * (C0 + C2) := by gcongr

end UnforcedLeray.Short.PartI.QcSmoothAux
