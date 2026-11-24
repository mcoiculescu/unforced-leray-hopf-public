import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields

/-!
# `PartIII-b:C/asrc/ra/8` : `RPerBound` from the bracket split and two estimates

Source of record: `the November 2 reference manuscript` (73 pages), 5022-5032
("`r_per` consists of distinct-center convection products and `(v - Σ_jV_j)` terms"), 4371
(`δ_base`), 4963-4977 (`V_j`, `h^p_A`), 2040-2051, 2152-2161 (the train).

With `b_j = [V_j, A^y_mer x_j]` (so `h^p_A = Σ_j b_j`, `hpA`) and `v = tr.v` the planar train:

* `rCross` : the distinct-center products `Σ_j Σ_{k≠j} (V_k·∇)b_j + (b_j·∇)V_k`;
* `rTrain` : the train terms `((v - ΣV_j)·∇)h^p_A + (h^p_A·∇)(v - ΣV_j)`;
* `RPerSplit` : `r_per = rCross + rTrain` (the single-center bracket identity of 5022-5025
  summed over `j`, with the full matrix retained);
* `RCrossBound`, `RTrainBound` : the cell-norm bounds `C δ_base M(A) s^{5/2}` of each part
  (Gaussian factors `e^{-c²/(16a)}` of the cross-center cells; train-to-Gaussian comparison at the
  BUC train `BgRegime.train_buc`), each with its own `(Csig, bsig, C, k, ν₀)`;
* `RPerSupport`, `RPerMeas` : `r_per = 0` for `s > 1.1/ν` (`A^y = 0` there) and a.e. strong
  measurability of `s·r_per`.

The combination of the two bounds (max/min of constants) is proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- The center bracket `b_j = [V_j, A^y_mer x_j]` (source 4971-4972). -/
def brk (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ × ℝ :=
  merApply (Ay ν χ A s) (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply (Ay ν χ A s) (xj ν j x))

/-- The Gaussian train `Σ_j V_j` (source 4963). -/
def vsum (ν s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := ∑' k : ℤ, Vj ν s k x

/-- **Distinct-center convection products** (source 5026-5027). -/
def rCross (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ∑' j : ℤ, ∑' k : ℤ, if k = j then 0 else
    (fderiv ℝ (brk ν χ A s j) x (Vj ν s k x) + fderiv ℝ (Vj ν s k) x (brk ν χ A s j x))

/-- **The `(v - Σ_jV_j)` terms** (source 5026-5027). -/
def rTrain {ν c : ℝ} (χ : ℝ → ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (A : ℝ → Mat3)
    (s : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  fderiv ℝ (hpA ν χ A s) x (trainPl tr s x - vsum ν s x) +
    fderiv ℝ (fun y => trainPl tr s y - vsum ν s y) x (hpA ν χ A s x)

/-- **Bracket split** (source 5022-5027): the single-center identity
`(∂_s + μ/s - νΔ)b_j + (V_j·∇)b_j + (b_j·∇)V_j = (f_A + e_A + ∇Ψ_A)_j` summed over `j` leaves
`r_per = rCross + rTrain` at every point of the cell, `s > 0`, for the train of a background regime. -/
def RPerSplit (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp →
    ∀ (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
      rPer μ χf p.train A s x = rCross p.ν χf A s x + rTrain χf p.train A s x

/-- **Cross-center bound** (source 5029-5031): Gaussian factors `e^{-c²/(16a)}`, `a ≤ 2.1`, on
`|x_j - x_k| ≥ c|j-k| - c/2`; cell norm `≤ C δ_base M(A) s^{5/2}`. -/
def RCrossBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (Csig bsig C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < bsig ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
        AEMeasurable (fun x => ENNReal.ofReal (‖toMer (rCross p.ν χf A s x)‖ ^ 2))
            (UnforcedLeray.Cyl.avgμ p.c) ∧
        ∫⁻ x, ENNReal.ofReal (‖toMer (rCross p.ν χf A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * deltaBase Csig bsig p.ν * affM p.ν χf A *
                s ^ (5 / 2 : ℝ)) ^ 2)

/-- **Train-to-Gaussian bound** (source 5029-5032, 2040-2051): the fixed-band comparison of the BUC
train with `Σ_jV_j` with finitely many derivatives bounds the `(v - ΣV_j)` terms by
`C δ_base M(A) s^{5/2}` in the cell norm. -/
def RTrainBound (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (Csig bsig C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < bsig ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A → ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
        AEMeasurable (fun x => ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2))
            (UnforcedLeray.Cyl.avgμ p.c) ∧
        ∫⁻ x, ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * deltaBase Csig bsig p.ν * affM p.ν χf A *
                s ^ (5 / 2 : ℝ)) ^ 2)

/-- `r_per = 0` for `s > 1.1/ν` (source 4953-4958: `A^y = χ_f A = 0` there, so `h^p_A, f_A, e_A,
Ψ_A` vanish on the open set `s > 1.1/ν`). -/
def RPerSupport (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp →
    ∀ (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
      ∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, rPer μ χf p.train A s x = 0

/-- `s·r_per` is a.e. strongly measurable for the source measure (continuity on `s > 0`, and
`rPerCoef = 0` for `s ≤ 0`... source 5023-5028). -/
def RPerMeas (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (p : Params) (d dm dp : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp →
    ∀ (μ : ℝ) (A : ℝ → Mat3), IsAffElem as A →
      AEStronglyMeasurable (rPerCoef μ χf p.train A) (srcMeasure p.c)

theorem toMer_add (a b : ℝ × ℝ) : toMer (a + b) = toMer a + toMer b := by
  ext i; fin_cases i <;> simp [toMer]

theorem norm_toMer_add_sq (a b : ℝ × ℝ) :
    ‖toMer (a + b)‖ ^ 2 ≤ 2 * ‖toMer a‖ ^ 2 + 2 * ‖toMer b‖ ^ 2 := by
  rw [toMer_add]
  have h := norm_add_le (toMer a) (toMer b)
  nlinarith [norm_nonneg (toMer a), norm_nonneg (toMer b), norm_nonneg (toMer a + toMer b),
    sq_nonneg (‖toMer a‖ - ‖toMer b‖)]

theorem deltaBase_mono {C₁ b₁ C₂ b₂ ν : ℝ} (hν : 0 < ν) (hC : C₁ ≤ C₂) (hb : b₂ ≤ b₁) :
    deltaBase C₁ b₁ ν ≤ deltaBase C₂ b₂ ν := by
  unfold deltaBase
  apply Real.exp_le_exp.2
  have h1 : C₁ / ν ≤ C₂ / ν := div_le_div_of_nonneg_right hC hν.le
  have h2 : b₂ * cOf ν ^ 2 ≤ b₁ * cOf ν ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  linarith

theorem deltaBase_nonneg (C b ν : ℝ) : 0 ≤ deltaBase C b ν := (Real.exp_pos _).le

theorem rPerBound_of (as : ℝ) (χf : ℝ → ℝ) (h1 : RPerSplit as χf) (h2 : RCrossBound as χf)
    (h3 : RTrainBound as χf) (h4 : RPerSupport as χf) (h5 : RPerMeas as χf) :
    RPerBound as χf := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨Cs1, bs1, C1, k1, n1, hb1, hn1, H1⟩ := h2 hχ K hK hKs dm dp hdm
  obtain ⟨Cs2, bs2, C2, k2, n2, hb2, hn2, H2⟩ := h3 hχ K hK hKs dm dp hdm
  refine ⟨max Cs1 Cs2, min bs1 bs2, 2 * (|C1| + |C2|), max k1 k2, min (min n1 n2) 1,
    lt_min hb1 hb2, lt_min (lt_min hn1 hn2) one_pos, ?_⟩
  intro p d hreg hν μ hμ A hA
  have hνp : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ n1 := le_trans hν ((min_le_left _ _).trans (min_le_left _ _))
  have hν2 : p.ν ≤ n2 := le_trans hν ((min_le_left _ _).trans (min_le_right _ _))
  have hν3 : p.ν ≤ 1 := le_trans hν (min_le_right _ _)
  refine ⟨h5 hχ p d dm dp hreg μ A hA, h4 hχ p d dm dp hreg μ A hA, ?_⟩
  intro s hs hs'
  obtain ⟨m1, b1⟩ := H1 p d hreg hν1 μ hμ A hA s hs hs'
  obtain ⟨m2, b2⟩ := H2 p d hreg hν2 μ hμ A hA s hs hs'
  have hsplit := h1 hχ p d dm dp hreg μ A hA s hs
  set δ := deltaBase (max Cs1 Cs2) (min bs1 bs2) p.ν with hδ
  set Y := p.ν⁻¹ ^ (max k1 k2) * δ * affM p.ν χf A * s ^ (5 / 2 : ℝ) with hY
  have hY0 : 0 ≤ Y := by
    have := affM_nonneg p.ν χf A
    have := deltaBase_nonneg (max Cs1 Cs2) (min bs1 bs2) p.ν
    have : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    positivity
  have hone : 1 ≤ p.ν⁻¹ := one_le_inv₀ hνp |>.2 hν3
  have hB : ∀ (C : ℝ) (k : ℕ) (Cs bs : ℝ), k ≤ max k1 k2 → Cs ≤ max Cs1 Cs2 → min bs1 bs2 ≤ bs →
      (C * p.ν⁻¹ ^ k * deltaBase Cs bs p.ν * affM p.ν χf A * s ^ (5 / 2 : ℝ)) ^ 2 ≤
        (|C| * Y) ^ 2 := by
    intro C k Cs bs hk hC hb
    have hd := deltaBase_mono hνp hC hb
    have hpw : p.ν⁻¹ ^ k ≤ p.ν⁻¹ ^ (max k1 k2) := pow_le_pow_right₀ hone hk
    have hm := affM_nonneg p.ν χf A
    have hs5 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
    have hd0 := deltaBase_nonneg Cs bs p.ν
    have hp0 : 0 ≤ p.ν⁻¹ ^ k := by positivity
    have hle : p.ν⁻¹ ^ k * deltaBase Cs bs p.ν * affM p.ν χf A * s ^ (5 / 2 : ℝ) ≤ Y := by
      rw [hY]
      apply mul_le_mul_of_nonneg_right _ hs5
      apply mul_le_mul_of_nonneg_right _ hm
      exact mul_le_mul hpw hd hd0 (by positivity)
    have hnn : 0 ≤ p.ν⁻¹ ^ k * deltaBase Cs bs p.ν * affM p.ν χf A * s ^ (5 / 2 : ℝ) := by
      positivity
    have : (C * p.ν⁻¹ ^ k * deltaBase Cs bs p.ν * affM p.ν χf A * s ^ (5 / 2 : ℝ)) ^ 2 =
        (|C| * (p.ν⁻¹ ^ k * deltaBase Cs bs p.ν * affM p.ν χf A * s ^ (5 / 2 : ℝ))) ^ 2 := by
      rw [show C * p.ν⁻¹ ^ k * deltaBase Cs bs p.ν * affM p.ν χf A *
        s ^ (5 / 2 : ℝ) = C * (p.ν⁻¹ ^ k * deltaBase Cs bs p.ν * affM p.ν χf A *
        s ^ (5 / 2 : ℝ)) by ring, mul_pow C, mul_pow |C|, sq_abs]
    rw [this]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hle (abs_nonneg _)) 2
  have e1 := hB C1 k1 Cs1 bs1 (le_max_left _ _) (le_max_left _ _) (min_le_left _ _)
  have e2 := hB C2 k2 Cs2 bs2 (le_max_right _ _) (le_max_right _ _) (min_le_right _ _)
  -- pointwise bound and integration
  have hpt : ∀ x, ENNReal.ofReal (‖toMer (rPer μ χf p.train A s x)‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖toMer (rCross p.ν χf A s x)‖ ^ 2) +
        2 * ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2) := by
    intro x
    rw [hsplit x]
    calc ENNReal.ofReal (‖toMer (rCross p.ν χf A s x + rTrain χf p.train A s x)‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖toMer (rCross p.ν χf A s x)‖ ^ 2 +
            2 * ‖toMer (rTrain χf p.train A s x)‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (norm_toMer_add_sq _ _)
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          simp
  calc ∫⁻ x, ENNReal.ofReal (‖toMer (rPer μ χf p.train A s x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
      ≤ ∫⁻ x, (2 * ENNReal.ofReal (‖toMer (rCross p.ν χf A s x)‖ ^ 2) +
          2 * ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2))
          ∂(UnforcedLeray.Cyl.avgμ p.c) := lintegral_mono hpt
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖toMer (rCross p.ν χf A s x)‖ ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c) +
        2 * ∫⁻ x, ENNReal.ofReal (‖toMer (rTrain χf p.train A s x)‖ ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c) := by
        rw [lintegral_add_left' (m1.const_mul 2), lintegral_const_mul'' _ m1,
          lintegral_const_mul'' _ m2]
    _ ≤ 2 * ENNReal.ofReal ((|C1| * Y) ^ 2) + 2 * ENNReal.ofReal ((|C2| * Y) ^ 2) := by
        gcongr
        · exact b1.trans (ENNReal.ofReal_le_ofReal e1)
        · exact b2.trans (ENNReal.ofReal_le_ofReal e2)
    _ ≤ ENNReal.ofReal ((2 * (|C1| + |C2|) * Y) ^ 2) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have a1 := abs_nonneg C1
        have a2 := abs_nonneg C2
        nlinarith [mul_nonneg a1 a2, sq_nonneg Y, mul_nonneg (mul_nonneg a1 a2) (sq_nonneg Y),
          mul_nonneg a1 hY0, mul_nonneg a2 hY0]
    _ = _ := by rw [hY]; ring_nf

end UnforcedLeray.Short.PartIIIb.Concrete
