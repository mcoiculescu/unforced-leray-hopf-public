import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2

/-!
# `PartIII-b:C/rep/5/1/1/3/2/2`: the box-to-general transfer, decomposed

Source `the November 2 reference manuscript`
3902-3912 (kernel pin on the dense class), 3905-3912.

`binDensityTransfer_of` proves `BinDensityTransfer` from three short facts:

* `VelBinGainLe` : the bin norm is bounded by `e^{|γ|/ν}` times the gain-normed `L²` norm (the
  inverse gain `g⁻¹ = e^{-γ s/(1+νs)}` lies between `e^{∓|γ|/ν}`);
* `AgeFiberNull` : fibres `{p.1 = x}` are `ageμ`-null (the mask `p.1 < S` at the bin end);
* `ThinBoxApprox` : a thin stress supported in a measurable age regime is approximated in the
  gain `Z`-norm by thin stresses whose first component is a box tensor vanishing off the regime
  and pointwise dominated by the original (window cut of `1_Q T₁`, as in `boxDenseZ`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Classical Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `velBin ≤ e^{|γ|/ν} ‖v‖` for `ν > 0` (source 3875, 5117: `g⁻¹ = e^{-γs/(1+νs)}`,
`|γ s/(1+νs)| ≤ |γ|/ν`, so `srcMeasure ≤ π e^{2|γ|/ν} · g⁻² ageμ`). -/
def VelBinGainLe : Prop :=
  ∀ (c γ ν s₀ s₁ : ℝ), 0 < ν → ∀ v : VelG c γ ν,
    velBin c s₀ s₁ (v : Chart → Merid) ≤
      ENNReal.ofReal (Real.exp (|γ| / ν)) * ENNReal.ofReal ‖v‖

/-- Age fibres are null for the age-weighted cylinder measure. -/
def AgeFiberNull : Prop := ∀ c b x : ℝ, ageμ c b {p : Chart | p.1 = x} = 0

/-- Box approximation of thin stresses supported in a measurable age regime (source 3905-3912;
the window cut of `boxDenseZ`, `NearInst/Masked/Proofs/BoxDenseZ.lean`, applied to `1_A T₁`). -/
def ThinBoxApprox : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 < c → 0 < ρb → ∀ (T : StrG c mZ ρb γ ν) (A : Set Chart), MeasurableSet A →
    thinPart T = T →
    (∀ᵐ p ∂(ageμ c (-1 / 2)), p ∉ A → (((T.fst : Lp Ten3 2 _)) : Chart → Ten3) p = 0) →
    ∃ (f : ℕ → Chart → Ten3) (G : ℕ → StrG c mZ ρb γ ν),
      (∀ n, NearInst.IsBoxTensor (f n)) ∧ (∀ n p, p ∉ A → f n p = 0) ∧
      (∀ n p, ‖f n p‖ ≤ ‖(((T.fst : Lp Ten3 2 _)) : Chart → Ten3) p‖) ∧
      (∀ n, strSum (G n) =ᵐ[ageμ c (-1 / 2)] f n) ∧
      Tendsto (fun n => ‖T - G n‖) atTop (𝓝 0)

theorem binDensityTransfer_of (h1 : VelBinGainLe) (h2 : AgeFiberNull) (h3 : ThinBoxApprox) :
    BinDensityTransfer := by
  intro Pl K hC0 L μ Q ep C k hQ hbox h s hh hhδ hs hsS Sf hSf T hT hsupp
  have hc : 0 < cOf L.ν := inv_pos.2 (pow_pos L.ν_pos 2)
  have hρb : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos (L.params Pl).ν_pos _)))
      (Real.exp_pos _)) (Real.rpow_pos_of_pos (L.params Pl).ε_pos _)
  have hAm : MeasurableSet {p : Chart | Q h s p.1} := measurable_fst (hQ h s)
  obtain ⟨f, G, hfbox, hfzero, hfle, hGs, hGlim⟩ :=
    h3 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hc hρb T {p : Chart | Q h s p.1} hAm hT
      (by filter_upwards [hsupp] with p hp hpA using hp hpA)
  set B : ℝ≥0∞ := ENNReal.ofReal (C * L.ν⁻¹ ^ k * L.ε ^ ep *
    (s ^ (1 / 2 : ℝ) + s ^ (3 / 4 : ℝ))) with hB
  set Z : ℝ≥0∞ := z1Part (cOf L.ν) K.mZ (fun t => Real.exp (K.δ - h) * s ≤ t ∧ Q h s t)
    (((T.fst : Lp Ten3 2 _)) : Chart → Ten3) with hZ
  have hbin : MeasurableSet {p : Chart | s * Real.exp (-h) < p.1 ∧ p.1 ≤ s} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have key : ∀ n, velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf (G n) : Chart → Merid) ≤ B * Z := by
    intro n
    have hb := hbox h s hh hhδ hs hsS (f n) (hfbox n) (fun p hp => hfzero n p hp)
    refine le_trans ?_ (hb.trans (mul_le_mul' le_rfl ?_))
    · apply le_of_eq
      unfold velBin
      congr 1
      apply setLIntegral_congr_fun_ae hbin
      have hnull : ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)), p.1 ≠ L.Scut K := by
        have := h2 (cOf L.ν) (-3 / 2) (L.Scut K)
        exact measure_eq_zero_iff_ae_notMem.1 this
      have hae := hSf (G n) (f n) (hfbox n) (hGs n)
      have hh' : ∀ᵐ p ∂(ageμ (cOf L.ν) (-3 / 2)), p ∈ {p : Chart | s * Real.exp (-h) < p.1 ∧
          p.1 ≤ s} → ‖(Sf (G n) : Chart → Merid) p‖ₑ ^ (2 : ℝ) =
          ‖(Real.sqrt p.1)⁻¹ • NearInst.merRe (-NearInst.sepWfar L.ν (μ : ℂ)
            L.ε⁻¹ K.δ p.1 (NearInst.cartLift L.ε⁻¹ (cOf L.ν) (f n)) (NearInst.chartY L.ε⁻¹ p)
            (NearInst.chartTau L.ε⁻¹ p))‖ₑ ^ (2 : ℝ) := by
        filter_upwards [hae, hnull] with p hp hn hpb
        have hlt : p.1 < L.Scut K := lt_of_le_of_ne (hpb.2.trans hsS) hn
        rw [hp]
        simp only [hlt, ite_true]
      exact Filter.Eventually.filter_mono (NearInst.ae_srcMeasure (cOf L.ν)).le hh'
    · unfold z1Part
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      apply lintegral_mono
      intro p
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      exact enorm_le_iff_norm_le.2 (hfle n p)
  have ha : Tendsto (fun n => ENNReal.ofReal (Real.exp (|gRate Pl| / L.ν)) *
      ENNReal.ofReal (‖Sf‖ * ‖T - G n‖)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => ENNReal.ofReal (‖Sf‖ * ‖T - G n‖)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal ((hGlim.const_mul ‖Sf‖))
      simpa using this
    have := ENNReal.Tendsto.const_mul h0
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (Real.exp (|gRate Pl| / L.ν)) ≠ ⊤))
    simpa using this
  have hlim : Tendsto (fun n => B * Z + ENNReal.ofReal (Real.exp (|gRate Pl| / L.ν)) *
      ENNReal.ofReal (‖Sf‖ * ‖T - G n‖)) atTop (𝓝 (B * Z + 0)) :=
    tendsto_const_nhds.add ha
  rw [add_zero] at hlim
  refine ge_of_tendsto' hlim fun n => ?_
  have hsplit : Sf T = Sf (G n) + Sf (T - G n) := by rw [← map_add]; congr 1; abel
  calc velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf T : Chart → Merid)
      = velBin (cOf L.ν) (s * Real.exp (-h)) s
          ((Sf (G n) + Sf (T - G n) : LVel Pl L) : Chart → Merid) := by rw [← hsplit]
    _ ≤ velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf (G n) : Chart → Merid) +
          velBin (cOf L.ν) (s * Real.exp (-h)) s (Sf (T - G n) : Chart → Merid) :=
        velBin_add_le _ _ _ _ _ _ _
    _ ≤ B * Z + ENNReal.ofReal (Real.exp (|gRate Pl| / L.ν)) *
          ENNReal.ofReal (‖Sf‖ * ‖T - G n‖) := by
        gcongr
        · exact key n
        · refine (h1 _ _ _ _ _ L.ν_pos _).trans ?_
          gcongr
          exact Sf.le_opNorm _

end UnforcedLeray.Short.PartIIIb.Concrete
