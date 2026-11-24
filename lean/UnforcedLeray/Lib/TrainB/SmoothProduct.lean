import UnforcedLeray.Lib.TrainB.WeakEmbedding

/-!
# First-order smooth product bounds for the train cylinder

These are the first concrete Leibniz terms needed by the H³ algebra estimate. The low-order
factor is controlled by the smooth H³-to-bounded estimate, and the other factor by its actual
H³ derivative component.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)

/-- Translate the two cylinder coordinate directions into B0151's horizontal/vertical bit. -/
def boolOfFin2 (i : Fin 2) : Bool := if i = 0 then true else false

theorem b0151WordFin_map_boolOfFin2 (w : List (Fin 2)) :
    UnforcedLeray.TrainB.b0151WordFin (w.map boolOfFin2) = w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      fin_cases i <;> simp [boolOfFin2, UnforcedLeray.TrainB.b0151WordFin, ih]

/-- B0151's recursive partial word agrees with the cylinder Sobolev word for any list of
coordinate directions, including words with repeated directions. -/
theorem b0151_derivWord_of_finWord {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (w : List (Fin 2)) :
    UnforcedLeray.B0151.derivWord (w.map boolOfFin2) f =
      UnforcedLeray.Sob.iterD (w.map UnforcedLeray.Sob.cylDir) f := by
  rw [b0151_derivWord_eq_iterD hf]
  congr 1
  calc
    UnforcedLeray.TrainB.b0151WordPlane (w.map boolOfFin2) =
        (UnforcedLeray.TrainB.b0151WordFin (w.map boolOfFin2)).map
          UnforcedLeray.Sob.cylDir :=
      (map_cylDir_b0151Word (w.map boolOfFin2)).symm
    _ = w.map UnforcedLeray.Sob.cylDir := by rw [b0151WordFin_map_boolOfFin2]

/-- Products of smooth compact-axial periodic scalar fields remain in the cylinder test class. -/
theorem IsCylSmooth.mul {c : ℝ} {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    UnforcedLeray.Sob.IsCylSmooth c (fun z => f z * g z) := by
  refine ⟨hf.smooth.mul hg.smooth, ?_, ?_⟩
  · intro z
    rw [hf.periodic z, hg.periodic z]
  · obtain ⟨R, hR⟩ := hf.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, zero_mul]⟩

/-- B0151's first derivative of a product, written with the cylinder derivative word. -/
theorem derivWord_singleton_mul {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (b : Bool) :
    UnforcedLeray.B0151.derivWord [b] (fun z => f z * g z) =
      fun z => UnforcedLeray.B0151.derivWord [b] f z * g z +
        f z * UnforcedLeray.B0151.derivWord [b] g z := by
  funext z
  cases b
  · exact UnforcedLeray.B0151.partialY_mul
      (hf.differentiable (by simp)) (hg.differentiable (by simp)) z
  · exact UnforcedLeray.B0151.partialX_mul
      (hf.differentiable (by simp)) (hg.differentiable (by simp)) z

/-- The one-step coordinate derivative of a sum. -/
theorem partialX_add {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    UnforcedLeray.GaussianVortex.partialX (fun x => f x + g x) z =
      UnforcedLeray.GaussianVortex.partialX f z +
        UnforcedLeray.GaussianVortex.partialX g z := by
  rcases z with ⟨x, y⟩
  exact ((UnforcedLeray.B0151.hasDerivAt_sliceX hf x y).add
    (UnforcedLeray.B0151.hasDerivAt_sliceX hg x y)).deriv

/-- The other one-step coordinate derivative of a sum. -/
theorem partialY_add {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    UnforcedLeray.GaussianVortex.partialY (fun x => f x + g x) z =
      UnforcedLeray.GaussianVortex.partialY f z +
        UnforcedLeray.GaussianVortex.partialY g z := by
  rcases z with ⟨x, y⟩
  exact ((UnforcedLeray.B0151.hasDerivAt_sliceY hf x y).add
    (UnforcedLeray.B0151.hasDerivAt_sliceY hg x y)).deriv

/-- The B0151 derivative word of length one commutes with a sum. -/
theorem derivWord_singleton_add {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (b : Bool) :
    UnforcedLeray.B0151.derivWord [b] (fun z => f z + g z) =
      fun z => UnforcedLeray.B0151.derivWord [b] f z +
        UnforcedLeray.B0151.derivWord [b] g z := by
  funext z
  cases b
  · exact partialY_add (hf.differentiable (by simp)) (hg.differentiable (by simp)) z
  · exact partialX_add (hf.differentiable (by simp)) (hg.differentiable (by simp)) z

/-- Exact two-step Leibniz expansion. Each pair records one choice of which factor receives each
derivative, so repeated coordinate directions retain their multiplicity. -/
theorem derivWord_pair_mul {c : ℝ} {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (a b : Bool) :
    UnforcedLeray.B0151.derivWord [b, a] (fun z => f z * g z) = fun z =>
      UnforcedLeray.B0151.derivWord [b, a] f z * g z +
      UnforcedLeray.B0151.derivWord [a] f z * UnforcedLeray.B0151.derivWord [b] g z +
      UnforcedLeray.B0151.derivWord [b] f z * UnforcedLeray.B0151.derivWord [a] g z +
      f z * UnforcedLeray.B0151.derivWord [b, a] g z := by
  have hfa := UnforcedLeray.B0151.contDiff_derivWord hf.smooth [a]
  have hga := UnforcedLeray.B0151.contDiff_derivWord hg.smooth [a]
  have hinner := derivWord_singleton_mul hf.smooth hg.smooth a
  have hsum := derivWord_singleton_add (hfa.mul hg.smooth) (hf.smooth.mul hga) b
  have hleft := derivWord_singleton_mul hfa hg.smooth b
  have hright := derivWord_singleton_mul hf.smooth hga b
  have hword (φ : Plane → ℝ) :
      UnforcedLeray.B0151.derivWord [b, a] φ =
        UnforcedLeray.B0151.derivWord [b] (UnforcedLeray.B0151.derivWord [a] φ) := by
    cases b <;> rfl
  rw [hword (fun z => f z * g z), hword f, hword g]
  change UnforcedLeray.B0151.derivWord [b]
    (UnforcedLeray.B0151.derivWord [a] (fun x => f x * g x)) = fun z => _
  rw [hinner, hsum, hleft, hright]
  funext z
  ring

/-- The derivative of a four-term smooth sum is the sum of the four derivatives. -/
theorem derivWord_singleton_add_four {A B C D : Plane → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hC : ContDiff ℝ ∞ C) (hD : ContDiff ℝ ∞ D) (b : Bool) :
    UnforcedLeray.B0151.derivWord [b] (fun z => A z + B z + C z + D z) =
      fun z => UnforcedLeray.B0151.derivWord [b] A z +
        UnforcedLeray.B0151.derivWord [b] B z +
        UnforcedLeray.B0151.derivWord [b] C z +
        UnforcedLeray.B0151.derivWord [b] D z := by
  have hgroup : (fun z => A z + B z + C z + D z) =
      (fun z => (A z + B z) + (C z + D z)) := by
    funext z
    ring
  rw [hgroup]
  have houter := derivWord_singleton_add (hA.add hB) (hC.add hD) b
  have hleft := derivWord_singleton_add hA hB b
  have hright := derivWord_singleton_add hC hD b
  rw [houter, hleft, hright]
  funext z
  ring

/-- Exact third-order Leibniz expansion. The eight terms are indexed by the eight choices of
which factor receives each derivative position. -/
theorem derivWord_triple_mul {c : ℝ} {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (a b d : Bool) :
    UnforcedLeray.B0151.derivWord [d, b, a] (fun z => f z * g z) = fun z =>
      UnforcedLeray.B0151.derivWord [d, b, a] f z * g z +
      UnforcedLeray.B0151.derivWord [b, a] f z * UnforcedLeray.B0151.derivWord [d] g z +
      UnforcedLeray.B0151.derivWord [d, a] f z * UnforcedLeray.B0151.derivWord [b] g z +
      UnforcedLeray.B0151.derivWord [a] f z * UnforcedLeray.B0151.derivWord [d, b] g z +
      UnforcedLeray.B0151.derivWord [d, b] f z * UnforcedLeray.B0151.derivWord [a] g z +
      UnforcedLeray.B0151.derivWord [b] f z * UnforcedLeray.B0151.derivWord [d, a] g z +
      UnforcedLeray.B0151.derivWord [d] f z * UnforcedLeray.B0151.derivWord [b, a] g z +
      f z * UnforcedLeray.B0151.derivWord [d, b, a] g z := by
  let A : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [b, a] f z * g z
  let B : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [a] f z *
    UnforcedLeray.B0151.derivWord [b] g z
  let C : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [b] f z *
    UnforcedLeray.B0151.derivWord [a] g z
  let D : Plane → ℝ := fun z => f z * UnforcedLeray.B0151.derivWord [b, a] g z
  have hA : ContDiff ℝ ∞ A := by
    dsimp [A]
    exact (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b, a]).mul hg.smooth
  have hB : ContDiff ℝ ∞ B := by
    dsimp [B]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [a])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b])
  have hC : ContDiff ℝ ∞ C := by
    dsimp [C]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [a])
  have hD : ContDiff ℝ ∞ D := by
    dsimp [D]
    exact hf.smooth.mul (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b, a])
  have hp := derivWord_pair_mul hf hg a b
  have hsum := derivWord_singleton_add_four hA hB hC hD d
  have htermA := derivWord_singleton_mul
    (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b, a]) hg.smooth d
  have htermB := derivWord_singleton_mul
    (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [a])
    (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b]) d
  have htermC := derivWord_singleton_mul
    (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b])
    (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [a]) d
  have htermD := derivWord_singleton_mul hf.smooth
    (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b, a]) d
  have hword (φ : Plane → ℝ) :
      UnforcedLeray.B0151.derivWord [d, b, a] φ =
        UnforcedLeray.B0151.derivWord [d] (UnforcedLeray.B0151.derivWord [b, a] φ) := by
    cases d <;> rfl
  have hword2 (e : Bool) (φ : Plane → ℝ) :
      UnforcedLeray.B0151.derivWord [d, e] φ =
        UnforcedLeray.B0151.derivWord [d] (UnforcedLeray.B0151.derivWord [e] φ) := by
    cases d <;> rfl
  rw [hword (fun z => f z * g z), hword f, hword g]
  rw [hword2 a f, hword2 b g, hword2 b f, hword2 a g]
  change UnforcedLeray.B0151.derivWord [d]
      (UnforcedLeray.B0151.derivWord [b, a] (fun z => f z * g z)) = _
  rw [hp, hsum, htermA, htermB, htermC, htermD]
  funext z
  dsimp [A, B, C, D]
  ring

/-- Minkowski bound for four summands, expressed in left-associated sum notation. -/
theorem eLpNorm_add_four_le {μ : Measure Plane} {A B C D : Plane → ℝ}
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hC : AEStronglyMeasurable C μ) (hD : AEStronglyMeasurable D μ) :
    eLpNorm (fun z => A z + B z + C z + D z) 2 μ ≤
      eLpNorm A 2 μ + eLpNorm B 2 μ + eLpNorm C 2 μ + eLpNorm D 2 μ := by
  have hgroup : (fun z => A z + B z + C z + D z) =
      (fun z => (A z + B z) + (C z + D z)) := by
    funext z
    ring
  rw [hgroup]
  have hAB := eLpNorm_add_le (μ := μ) hA hB (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hCD := eLpNorm_add_le (μ := μ) hC hD (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfunAB : (fun z => A z + B z) = A + B := by funext z; rfl
  have hfunCD : (fun z => C z + D z) = C + D := by funext z; rfl
  have hAB' : eLpNorm (fun z => A z + B z) 2 μ ≤ eLpNorm A 2 μ + eLpNorm B 2 μ := by
    rw [hfunAB]
    exact hAB
  have hCD' : eLpNorm (fun z => C z + D z) 2 μ ≤ eLpNorm C 2 μ + eLpNorm D 2 μ := by
    rw [hfunCD]
    exact hCD
  calc
    eLpNorm (fun z => (A z + B z) + (C z + D z)) 2 μ ≤
      eLpNorm (fun z => A z + B z) 2 μ + eLpNorm (fun z => C z + D z) 2 μ :=
        eLpNorm_add_le (μ := μ) (hA.add hB) (hC.add hD)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ (eLpNorm A 2 μ + eLpNorm B 2 μ) +
        (eLpNorm C 2 μ + eLpNorm D 2 μ) := add_le_add hAB' hCD'
    _ = eLpNorm A 2 μ + eLpNorm B 2 μ + eLpNorm C 2 μ + eLpNorm D 2 μ := by ac_rfl

/-- Minkowski bound for eight summands. -/
theorem eLpNorm_add_eight_le {μ : Measure Plane} {A B C D E F G H : Plane → ℝ}
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ)
    (hC : AEStronglyMeasurable C μ) (hD : AEStronglyMeasurable D μ)
    (hE : AEStronglyMeasurable E μ) (hF : AEStronglyMeasurable F μ)
    (hG : AEStronglyMeasurable G μ) (hH : AEStronglyMeasurable H μ) :
    eLpNorm (fun z => A z + B z + C z + D z + E z + F z + G z + H z) 2 μ ≤
      eLpNorm A 2 μ + eLpNorm B 2 μ + eLpNorm C 2 μ + eLpNorm D 2 μ +
        eLpNorm E 2 μ + eLpNorm F 2 μ + eLpNorm G 2 μ + eLpNorm H 2 μ := by
  have hgroup : (fun z => A z + B z + C z + D z + E z + F z + G z + H z) =
      (fun z => (A z + B z + C z + D z) + (E z + F z + G z + H z)) := by
    funext z
    ring
  rw [hgroup]
  have hleft := eLpNorm_add_four_le hA hB hC hD
  have hright := eLpNorm_add_four_le hE hF hG hH
  calc
    eLpNorm (fun z => (A z + B z + C z + D z) + (E z + F z + G z + H z)) 2 μ ≤
      eLpNorm (fun z => A z + B z + C z + D z) 2 μ +
        eLpNorm (fun z => E z + F z + G z + H z) 2 μ :=
      eLpNorm_add_le (μ := μ) (((hA.add hB).add hC).add hD)
        (((hE.add hF).add hG).add hH) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ (eLpNorm A 2 μ + eLpNorm B 2 μ + eLpNorm C 2 μ + eLpNorm D 2 μ) +
        (eLpNorm E 2 μ + eLpNorm F 2 μ + eLpNorm G 2 μ + eLpNorm H 2 μ) :=
      add_le_add hleft hright
    _ = _ := by ac_rfl

/-- Any B0151 word of length at most three applied to a smooth periodic field has its centered-cell
L² norm bounded by the H³ norm.  Cell conversion is used only for the periodic derivative. -/
theorem smooth_h3_derivWord_eLp_bound {c : ℝ} (hc1 : 1 ≤ c) {f : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (w : List Bool) (hw : w.length ≤ 3) :
    eLpNorm (UnforcedLeray.B0151.derivWord w f) 2 (UnforcedLeray.B0151.cellMeasure c) ≤
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) f hf‖ := by
  have hc : 0 < c := by linarith [hc1]
  have hp0 : UnforcedLeray.B0151.IsPeriodicQ c f := by
    intro q η
    simpa [UnforcedLeray.B0151.IsPeriodicQ] using hf.periodic (q, η)
  have hper : UnforcedLeray.Cyl.IsPeriodic c (UnforcedLeray.B0151.derivWord w f) := by
    intro z
    rcases z with ⟨q, η⟩
    change UnforcedLeray.B0151.derivWord w f (q + c, η) =
      UnforcedLeray.B0151.derivWord w f (q, η)
    exact UnforcedLeray.B0151.periodic_derivWord hp0 w q η
  have hmeas : Measurable (UnforcedLeray.B0151.derivWord w f) :=
    (UnforcedLeray.B0151.contDiff_derivWord hf.smooth w).continuous.measurable
  let α : UnforcedLeray.Sob.Idx 2 3 := UnforcedLeray.Sob.Idx.ofList
    (b0151WordFin w) (by simpa only [b0151WordFin_length] using hw)
  have hword := cylinder_word_of_b0151Word (c := c) w hw
  have hcenter := smooth_iterD_eLp_le_h3norm hc hf (b0151WordPlane w) α hword
  calc
    eLpNorm (UnforcedLeray.B0151.derivWord w f) 2
        (UnforcedLeray.B0151.cellMeasure c) =
      eLpNorm (UnforcedLeray.B0151.derivWord w f) 2 (UnforcedLeray.Cyl.cellμ c) :=
        eLpNorm_sq_b0151_eq_cyl hc hmeas hper
    _ = eLpNorm (UnforcedLeray.Sob.iterD (b0151WordPlane w) f) 2
        (UnforcedLeray.Cyl.cellμ c) := by rw [b0151_derivWord_eq_iterD hf.smooth w]
    _ ≤ _ := hcenter

/-- Every Leibniz term whose total derivative order is at most three is bounded by a low-order
H³ multiplier and the other factor's actual H³ derivative component. -/
theorem smooth_h3_product_term_bound {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (u v : List Bool) (hu : u.length ≤ 3) (hv : v.length ≤ 3)
    (htotal : u.length + v.length ≤ 3) :
    eLpNorm (fun z => UnforcedLeray.B0151.derivWord u f z *
      UnforcedLeray.B0151.derivWord v g z) 2 (UnforcedLeray.B0151.cellMeasure c) ≤
      ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) f hf‖) *
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) g hg‖ := by
  have hc : 0 < c := by linarith [hc1]
  have hsum : u.length ≤ 1 ∨ v.length ≤ 1 := by omega
  rcases hsum with hu1 | hv1
  · have hlow := smooth_h3_lowDerivative_mul_L2 (f := f)
      (g := UnforcedLeray.B0151.derivWord v g) hc1 hf u hu1
    have hhigh := smooth_h3_derivWord_eLp_bound hc1 hg v hv
    calc
      eLpNorm (fun z => UnforcedLeray.B0151.derivWord u f z *
          UnforcedLeray.B0151.derivWord v g z) 2 (UnforcedLeray.B0151.cellMeasure c) ≤
        ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
          (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖) *
          eLpNorm (UnforcedLeray.B0151.derivWord v g) 2
            (UnforcedLeray.B0151.cellMeasure c) := hlow
      _ ≤ _ := by gcongr
  · have hlow := smooth_h3_lowDerivative_mul_L2 (f := g)
      (g := UnforcedLeray.B0151.derivWord u f) hc1 hg v hv1
    have hhigh := smooth_h3_derivWord_eLp_bound hc1 hf u hu
    have hcomm : (fun z => UnforcedLeray.B0151.derivWord u f z *
        UnforcedLeray.B0151.derivWord v g z) =
        (fun z => UnforcedLeray.B0151.derivWord v g z *
          UnforcedLeray.B0151.derivWord u f z) := by
      funext z
      exact mul_comm _ _
    rw [hcomm]
    calc
      eLpNorm (fun z => UnforcedLeray.B0151.derivWord v g z *
          UnforcedLeray.B0151.derivWord u f z) 2 (UnforcedLeray.B0151.cellMeasure c) ≤
        ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
          (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg‖) *
          eLpNorm (UnforcedLeray.B0151.derivWord u f) 2
            (UnforcedLeray.B0151.cellMeasure c) := hlow
      _ ≤ ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
          (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg‖) *
          ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
            (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ := by
            gcongr
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 12),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 12)]
        ac_rfl

/-- Common scalar coefficient for the smooth H³ product Leibniz terms. -/
def smoothH3ProductFactor {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    ℝ≥0∞ :=
  ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
    (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
    (by linarith [hc1]) f hf‖) * ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth
    (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) g hg‖

/-- The four terms in an order-two Leibniz expansion are each bounded by the same product of H³
norms. The resulting L² bound is stated as a fourfold sum to keep the ENNReal arithmetic direct. -/
theorem smooth_h3_pair_mul_eLp_bound {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (a b : Bool) :
    eLpNorm (UnforcedLeray.B0151.derivWord [b, a] (fun z => f z * g z)) 2
        (UnforcedLeray.B0151.cellMeasure c) ≤
      smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg := by
  let K := ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
    (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
    (by linarith [hc1]) f hf‖) * ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth
      (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) g hg‖
  let A : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [b, a] f z * g z
  let B : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [a] f z *
    UnforcedLeray.B0151.derivWord [b] g z
  let C : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [b] f z *
    UnforcedLeray.B0151.derivWord [a] g z
  let D : Plane → ℝ := fun z => f z * UnforcedLeray.B0151.derivWord [b, a] g z
  have hA : ContDiff ℝ ∞ A := by
    dsimp [A]
    exact (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b, a]).mul hg.smooth
  have hB : ContDiff ℝ ∞ B := by
    dsimp [B]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [a])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b])
  have hC : ContDiff ℝ ∞ C := by
    dsimp [C]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [a])
  have hD : ContDiff ℝ ∞ D := by
    dsimp [D]
    exact hf.smooth.mul (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b, a])
  have hA0 := smooth_h3_product_term_bound hc1 hf hg [b, a] [] (by simp) (by simp) (by simp)
  have hB0 := smooth_h3_product_term_bound hc1 hf hg [a] [b] (by simp) (by simp) (by simp)
  have hC0 := smooth_h3_product_term_bound hc1 hf hg [b] [a] (by simp) (by simp) (by simp)
  have hD0 := smooth_h3_product_term_bound hc1 hf hg [] [b, a] (by simp) (by simp) (by simp)
  have hformula := derivWord_pair_mul hf hg a b
  have heq : UnforcedLeray.B0151.derivWord [b, a] (fun z => f z * g z) =
      (fun z => A z + B z + C z + D z) := by
    rw [hformula]
  calc
    eLpNorm (UnforcedLeray.B0151.derivWord [b, a] (fun z => f z * g z)) 2
        (UnforcedLeray.B0151.cellMeasure c) = eLpNorm (fun z => A z + B z + C z + D z) 2
        (UnforcedLeray.B0151.cellMeasure c) := by rw [heq]
    _ ≤ eLpNorm A 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm B 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm C 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm D 2 (UnforcedLeray.B0151.cellMeasure c) :=
      eLpNorm_add_four_le hA.continuous.aestronglyMeasurable
        hB.continuous.aestronglyMeasurable hC.continuous.aestronglyMeasurable
        hD.continuous.aestronglyMeasurable
    _ ≤ K + K + K + K := by
      dsimp [A, B, C, D, K, smoothH3ProductFactor]
      exact (add_le_add (add_le_add (add_le_add hA0 hB0) hC0) hD0)

/-- The eight terms in an order-three Leibniz expansion are each bounded by the same product of H³
norms. This is the top-order smooth product estimate used by the cylinder H³ algebra bound. -/
theorem smooth_h3_triple_mul_eLp_bound {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (a b d : Bool) :
    eLpNorm (UnforcedLeray.B0151.derivWord [d, b, a] (fun z => f z * g z)) 2
        (UnforcedLeray.B0151.cellMeasure c) ≤
      (smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg) +
      (smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg) := by
  let K := smoothH3ProductFactor hc1 hf hg
  let A : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [d, b, a] f z * g z
  let B : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [b, a] f z *
    UnforcedLeray.B0151.derivWord [d] g z
  let C : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [d, a] f z *
    UnforcedLeray.B0151.derivWord [b] g z
  let D : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [a] f z *
    UnforcedLeray.B0151.derivWord [d, b] g z
  let E : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [d, b] f z *
    UnforcedLeray.B0151.derivWord [a] g z
  let F : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [b] f z *
    UnforcedLeray.B0151.derivWord [d, a] g z
  let G : Plane → ℝ := fun z => UnforcedLeray.B0151.derivWord [d] f z *
    UnforcedLeray.B0151.derivWord [b, a] g z
  let H : Plane → ℝ := fun z => f z * UnforcedLeray.B0151.derivWord [d, b, a] g z
  have hA : ContDiff ℝ ∞ A := by
    dsimp [A]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [d, b, a]) hg.smooth
  have hB : ContDiff ℝ ∞ B := by
    dsimp [B]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b, a])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [d])
  have hC : ContDiff ℝ ∞ C := by
    dsimp [C]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [d, a])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b])
  have hD : ContDiff ℝ ∞ D := by
    dsimp [D]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [a])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [d, b])
  have hE : ContDiff ℝ ∞ E := by
    dsimp [E]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [d, b])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [a])
  have hF : ContDiff ℝ ∞ F := by
    dsimp [F]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [d, a])
  have hG : ContDiff ℝ ∞ G := by
    dsimp [G]
    exact ContDiff.mul (UnforcedLeray.B0151.contDiff_derivWord hf.smooth [d])
      (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b, a])
  have hH : ContDiff ℝ ∞ H := by
    dsimp [H]
    exact ContDiff.mul hf.smooth (UnforcedLeray.B0151.contDiff_derivWord hg.smooth [d, b, a])
  have hA0 := smooth_h3_product_term_bound hc1 hf hg [d, b, a] [] (by simp) (by simp) (by simp)
  have hB0 := smooth_h3_product_term_bound hc1 hf hg [b, a] [d] (by simp) (by simp) (by simp)
  have hC0 := smooth_h3_product_term_bound hc1 hf hg [d, a] [b] (by simp) (by simp) (by simp)
  have hD0 := smooth_h3_product_term_bound hc1 hf hg [a] [d, b] (by simp) (by simp) (by simp)
  have hE0 := smooth_h3_product_term_bound hc1 hf hg [d, b] [a] (by simp) (by simp) (by simp)
  have hF0 := smooth_h3_product_term_bound hc1 hf hg [b] [d, a] (by simp) (by simp) (by simp)
  have hG0 := smooth_h3_product_term_bound hc1 hf hg [d] [b, a] (by simp) (by simp) (by simp)
  have hH0 := smooth_h3_product_term_bound hc1 hf hg [] [d, b, a] (by simp) (by simp) (by simp)
  have hformula := derivWord_triple_mul hf hg a b d
  have heq : UnforcedLeray.B0151.derivWord [d, b, a] (fun z => f z * g z) =
      (fun z => A z + B z + C z + D z + E z + F z + G z + H z) := by
    rw [hformula]
  calc
    eLpNorm (UnforcedLeray.B0151.derivWord [d, b, a] (fun z => f z * g z)) 2
        (UnforcedLeray.B0151.cellMeasure c) =
      eLpNorm (fun z => A z + B z + C z + D z + E z + F z + G z + H z) 2
        (UnforcedLeray.B0151.cellMeasure c) := by rw [heq]
    _ ≤ _ := eLpNorm_add_eight_le
      hA.continuous.aestronglyMeasurable hB.continuous.aestronglyMeasurable
      hC.continuous.aestronglyMeasurable hD.continuous.aestronglyMeasurable
      hE.continuous.aestronglyMeasurable hF.continuous.aestronglyMeasurable
      hG.continuous.aestronglyMeasurable hH.continuous.aestronglyMeasurable
    _ ≤ _ := by
      have hleft : eLpNorm A 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm B 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm C 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm D 2 (UnforcedLeray.B0151.cellMeasure c) ≤ K + K + K + K := by
        dsimp [A, B, C, D, K, smoothH3ProductFactor]
        exact add_le_add (add_le_add (add_le_add hA0 hB0) hC0) hD0
      have hright : eLpNorm E 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm F 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm G 2 (UnforcedLeray.B0151.cellMeasure c) +
          eLpNorm H 2 (UnforcedLeray.B0151.cellMeasure c) ≤ K + K + K + K := by
        dsimp [E, F, G, H, K, smoothH3ProductFactor]
        exact add_le_add (add_le_add (add_le_add hE0 hF0) hG0) hH0
      calc
        eLpNorm A 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm B 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm C 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm D 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm E 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm F 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm G 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm H 2 (UnforcedLeray.B0151.cellMeasure c) =
          (eLpNorm A 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm B 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm C 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm D 2 (UnforcedLeray.B0151.cellMeasure c)) +
            (eLpNorm E 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm F 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm G 2 (UnforcedLeray.B0151.cellMeasure c) +
            eLpNorm H 2 (UnforcedLeray.B0151.cellMeasure c)) := by ac_rfl
        _ ≤ (K + K + K + K) + (K + K + K + K) := add_le_add hleft hright
        _ = _ := by ac_rfl

/-- One first-order derivative of a scalar product is L², with an explicit H³ product bound on
B0151's unnormalized period cell.  Both factors in the statement are genuine smooth cylinder
fields, so the derivative terms are periodic and their cell norm transfers are valid. -/
theorem smooth_h3_partial_mul_eLp_bound {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (b : Bool) :
    eLpNorm (UnforcedLeray.B0151.derivWord [b] (fun z => f z * g z)) 2
        (UnforcedLeray.B0151.cellMeasure c) ≤
      ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) f hf‖) *
          ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
        (by linarith [hc1]) g hg‖ * 2 := by
  have hc : 0 < c := by linarith [hc1]
  have hf1 := smooth_h3_lowDerivative_mul_L2 (f := f) (g := g) hc1 hf [b] (by simp)
  have hg0 := smooth_h3_lowDerivative_mul_L2 (f := g) (g := f) hc1 hg [b] (by simp)
  have hfg0 := smooth_h3_derivWord_eLp_bound hc1 hg [] (by simp)
  have hff0 := smooth_h3_derivWord_eLp_bound hc1 hf [] (by simp)
  have hfg : eLpNorm g 2 (UnforcedLeray.B0151.cellMeasure c) ≤
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg‖ := by
    simpa [UnforcedLeray.B0151.derivWord] using hfg0
  have hff : eLpNorm f 2 (UnforcedLeray.B0151.cellMeasure c) ≤
      ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ := by
    simpa [UnforcedLeray.B0151.derivWord] using hff0
  have hformula := derivWord_singleton_mul hf.smooth hg.smooth b
  have hsum := eLpNorm_add_le (μ := UnforcedLeray.B0151.cellMeasure c)
    ((UnforcedLeray.B0151.contDiff_derivWord hf.smooth [b]).continuous.aestronglyMeasurable.mul
      (hg.smooth.continuous.aestronglyMeasurable))
    (hf.smooth.continuous.aestronglyMeasurable.mul
      ((UnforcedLeray.B0151.contDiff_derivWord hg.smooth [b]).continuous.aestronglyMeasurable))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [hformula]
  calc
    eLpNorm (fun z => UnforcedLeray.B0151.derivWord [b] f z * g z +
        f z * UnforcedLeray.B0151.derivWord [b] g z) 2
        (UnforcedLeray.B0151.cellMeasure c) ≤
      eLpNorm (fun z => UnforcedLeray.B0151.derivWord [b] f z * g z) 2
          (UnforcedLeray.B0151.cellMeasure c) +
        eLpNorm (fun z => f z * UnforcedLeray.B0151.derivWord [b] g z) 2
          (UnforcedLeray.B0151.cellMeasure c) := hsum
    _ ≤ ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖) *
          eLpNorm g 2 (UnforcedLeray.B0151.cellMeasure c) +
        ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg‖) *
          eLpNorm f 2 (UnforcedLeray.B0151.cellMeasure c) := by
              exact add_le_add hf1 (by simpa [mul_comm] using hg0)
    _ ≤ ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖) *
          ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg‖ +
        ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg‖) *
          ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖ := by
          gcongr
    _ = ENNReal.ofReal (12 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf‖) *
          ENNReal.ofReal ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ)
        (k := 3) (p := 2) (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg‖ * 2 := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 12)]
          simp [mul_left_comm, mul_comm, two_mul]

/-- Every B0151 derivative of a smooth product through order three has a uniform L² bound.
The deliberately loose eightfold sum covers all ordered words in the H³ graph norm. -/
theorem smooth_h3_derivWord_mul_eLp_bound {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (w : List Bool) (hw : w.length ≤ 3) :
    eLpNorm (UnforcedLeray.B0151.derivWord w (fun z => f z * g z)) 2
        (UnforcedLeray.B0151.cellMeasure c) ≤
      smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg := by
  let K := smoothH3ProductFactor hc1 hf hg
  change eLpNorm (UnforcedLeray.B0151.derivWord w (fun z => f z * g z)) 2
      (UnforcedLeray.B0151.cellMeasure c) ≤ K + K + K + K + K + K + K + K
  have hK : K ≤ K + K := by
    calc
      K = K + 0 := by simp
      _ ≤ K + K := by simpa using add_le_add_left (show (0 : ℝ≥0∞) ≤ K from bot_le) K
  have h2 : K + K ≤ K + K + K + K := by
    calc
      K + K = (K + K) + 0 := by simp
      _ ≤ (K + K) + (K + K) := by
        simpa using add_le_add_left (show (0 : ℝ≥0∞) ≤ K + K from bot_le) (K + K)
      _ = K + K + K + K := by ac_rfl
  have h4 : K + K + K + K ≤ K + K + K + K + K + K + K + K := by
    calc
      K + K + K + K = (K + K + K + K) + 0 := by simp
      _ ≤ (K + K + K + K) + (K + K + K + K) := by
        simpa using add_le_add_left (show (0 : ℝ≥0∞) ≤ K + K + K + K from bot_le)
          (K + K + K + K)
      _ = K + K + K + K + K + K + K + K := by ac_rfl
  have h0 : K ≤ K + K + K + K + K + K + K + K := hK.trans (h2.trans h4)
  have h2x : K + K ≤ K + K + K + K + K + K + K + K := h2.trans h4
  cases w with
  | nil =>
      have h := smooth_h3_product_term_bound hc1 hf hg [] [] (by simp) (by simp) (by simp)
      calc
        _ ≤ K := by simpa [UnforcedLeray.B0151.derivWord, K, smoothH3ProductFactor] using h
        _ ≤ _ := h0
  | cons a w =>
    cases w with
    | nil =>
        have h := smooth_h3_partial_mul_eLp_bound hc1 hf hg a
        have h' : eLpNorm (UnforcedLeray.B0151.derivWord [a]
            (fun z => f z * g z)) 2 (UnforcedLeray.B0151.cellMeasure c) ≤ K * 2 := by
          simpa [K, smoothH3ProductFactor] using h
        calc
          _ ≤ K * 2 := h'
          _ = K + K := by rw [mul_two]
          _ ≤ _ := h2x
    | cons b w =>
      cases w with
      | nil =>
          have h := smooth_h3_pair_mul_eLp_bound hc1 hf hg b a
          have h' : eLpNorm (UnforcedLeray.B0151.derivWord [a, b]
              (fun z => f z * g z)) 2 (UnforcedLeray.B0151.cellMeasure c) ≤ K + K + K + K := by
            simpa [K, smoothH3ProductFactor] using h
          exact h'.trans h4
      | cons d w =>
        cases w with
        | nil =>
            have h := smooth_h3_triple_mul_eLp_bound hc1 hf hg d b a
            simpa [K, add_assoc] using h
        | cons e w =>
            simp only [List.length_cons] at hw
            omega

/-- The same uniform eight-term estimate holds for every ordered coordinate derivative word in
`H³`, now on the centered train cell. -/
theorem smooth_h3_iterD_mul_eLp_bound {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g)
    (w : List (Fin 2)) (hw : w.length ≤ 3) :
    eLpNorm (UnforcedLeray.Sob.iterD (w.map UnforcedLeray.Sob.cylDir)
      (fun z => f z * g z)) 2 (UnforcedLeray.Cyl.cellμ c) ≤
      smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg := by
  have hc : 0 < c := by linarith [hc1]
  let b := w.map boolOfFin2
  have hbase : UnforcedLeray.B0151.IsPeriodicQ c (fun z => f z * g z) := by
    intro q η
    simpa [UnforcedLeray.B0151.IsPeriodicQ] using
      (IsCylSmooth.mul hf hg).periodic (q, η)
  have hper : UnforcedLeray.Cyl.IsPeriodic c
      (UnforcedLeray.B0151.derivWord b (fun z => f z * g z)) := by
    intro z
    rcases z with ⟨q, η⟩
    change UnforcedLeray.B0151.derivWord b (fun z => f z * g z) (q + c, η) = _
    exact UnforcedLeray.B0151.periodic_derivWord hbase b q η
  have hmeas : Measurable (UnforcedLeray.B0151.derivWord b (fun z => f z * g z)) :=
    (UnforcedLeray.B0151.contDiff_derivWord ((IsCylSmooth.mul hf hg).smooth) b).continuous.measurable
  have hcell := smooth_h3_derivWord_mul_eLp_bound hc1 hf hg b (by simpa [b] using hw)
  rw [← b0151_derivWord_of_finWord ((IsCylSmooth.mul hf hg).smooth) w]
  rw [← eLpNorm_sq_b0151_eq_cyl hc hmeas hper]
  exact hcell

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.smooth_h3_pair_mul_eLp_bound
#print axioms UnforcedLeray.TrainB.smooth_h3_triple_mul_eLp_bound
#print axioms UnforcedLeray.TrainB.smooth_h3_partial_mul_eLp_bound
#print axioms UnforcedLeray.TrainB.IsCylSmooth.mul
#print axioms UnforcedLeray.TrainB.b0151_derivWord_of_finWord
#print axioms UnforcedLeray.TrainB.smooth_h3_derivWord_mul_eLp_bound
#print axioms UnforcedLeray.TrainB.smooth_h3_iterD_mul_eLp_bound
