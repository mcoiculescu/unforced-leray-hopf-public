import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.OpBoundOfBox

/-!
# `maskedSupport_of`: the mask keeps only `t ≤ e^δ s` (source 3905-3912)

Route: `opNorm_le_of_box` with `B = 0`, applied to `X = outRestr (ageBelow T) ∘ (Seps - Sf) ∘
inRestr (ageAbove (e^δ T))`. For box-type `F`, the input restriction gives a box tensor
`f' = 1_{t ≥ e^δ T} f`; the stress realization `hK` and the far pin give `Seps G = fullOut f'` and
`Sf G = farOut f'` a.e. For outputs `s < T ≤ S` the two kernels coincide: the mask in `sepWfar`
is true wherever the tensor is nonzero, since there `s_{chart} = R²/(z₀²+z₁²) ≥ e^δ T > e^δ s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The `htRho` measure has the same null sets as `ageμ`. -/
theorem ae_htRho_iff {c ρb : ℝ} (hρ : 0 < ρb) (P : Chart → Prop) :
    (∀ᵐ x ∂htRhoMeasure c ρb, P x) ↔ ∀ᵐ x ∂ageμ c (-1 / 2), P x := by
  simp only [htRhoMeasure]
  rw [Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne']

/-- Input restriction on the sum: `zsum (1_A F) = 1_A (zsum F)` `ageμ`-a.e. -/
theorem zsum_inRestr_ae {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (A : Set Chart)
    (hA : MeasurableSet A) (F : Zsp c mZ ρb) :
    ∀ᵐ x ∂ageμ c (-1 / 2), zsum (inRestr c mZ ρb A F) x = ind A x • zsum F x := by
  have hle1 : ageμ c (-1 / 2) ≤ z1Measure c mZ := by simpa using ageμ_le_z1Measure hmZ
  have h1 := ae_mono hle1 (restrLp_ae (μ := z1Measure c mZ) hA (zEquiv c mZ ρb F).1)
  have h2 := (ae_htRho_iff hρ _).1
    (restrLp_ae (μ := htRhoMeasure c ρb) hA (zEquiv c mZ ρb F).2)
  filter_upwards [h1, h2] with x hx1 hx2
  have hx1' : ((restrLp (z1Measure c mZ) Ten3 A (zEquiv c mZ ρb F).1 : Chart → Ten3) x) =
      ind A x • ((zEquiv c mZ ρb F).1 : Chart → Ten3) x := hx1
  have hx2' : ((restrLp (htRhoMeasure c ρb) Ten3 A (zEquiv c mZ ρb F).2 : Chart → Ten3) x) =
      ind A x • ((zEquiv c mZ ρb F).2 : Chart → Ten3) x := hx2
  have hz : ∀ H : Zsp c mZ ρb, ∀ y : Chart, zsum H y =
      (zEquiv c mZ ρb H).1 y + (zEquiv c mZ ρb H).2 y := fun H y => rfl
  rw [hz, hz, zEquiv_inRestr]
  dsimp only
  rw [hx1', hx2', smul_add]

/-- The chart point of `(z, τ)` has `s`-coordinate `R²/(z₀²+z₁²)`. -/
theorem chartOf_fst_eq (R c : ℝ) (z : Space) (τ : ℝ) :
    (chartOf R c z τ).1 = R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) := by
  simp only [chartOf, hRad]
  rw [Real.sq_sqrt (by positivity)]

/-- The zero tensor has zero Cartesian lift. -/
theorem nsSym_zero_eq : nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ]

/-- The masked far kernel equals the unmasked kernel on outputs `s < T ≤ S`, for tensors vanishing
below `e^δ T`. -/
theorem farOut_eq_fullOut_of_lt {R c ν μ δ S T : ℝ} (hδ : 0 < δ) (hTS : T ≤ S)
    (f : Chart → Ten3) (hf : ∀ p : Chart, p.1 < Real.exp δ * T → f p = 0) (x : Chart)
    (hx : x.1 < T) : farOut R c ν μ δ S f x = fullOut R c ν μ f x := by
  have hxS : x.1 < S := lt_of_lt_of_le hx hTS
  have hfun : (fun τ' z => if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)
      then cartLift R c f τ' z else 0) = cartLift R c f := by
    funext τ' z
    split_ifs with hc
    · rfl
    · have hchart : (chartOf R c z τ').1 < Real.exp δ * T := by
        rw [chartOf_fst_eq]
        exact lt_of_le_of_lt (not_lt.mp hc) (mul_lt_mul_of_pos_left hx (Real.exp_pos δ))
      have h0 : f (chartOf R c z τ') = 0 := hf _ hchart
      simp [cartLift, h0, nsSym_zero_eq]
  unfold farOut fullOut
  rw [if_pos hxS]
  unfold sepWfar
  rw [hfun]

/-- **`maskedSupport_of`** (source 3905-3912): the masked free bound has no input `t ≥ e^δ T` at
outputs `s < T ≤ S`. -/
theorem maskedSupport_of (hK : StressKernelRealization) (hD : BoxDenseZ) : MaskedSupport := by
  intro p mZ ρb μ δ S T hmZ hρ hρ1 hμ hδ hT hTS Seps Sf hpair
  obtain ⟨⟨Seps', hstress, htrans⟩, hfar⟩ := hpair
  have hX : ‖outRestr p.c (ageBelow T) ∘L (Seps - Sf) ∘L
      inRestr p.c mZ ρb (ageAbove (Real.exp δ * T))‖ ≤ 0 := by
    refine opNorm_le_of_box hD p.c_pos hmZ hρ hρ1 _ le_rfl ?_
    intro F f hf hFf
    have hA : MeasurableSet (ageAbove (Real.exp δ * T)) :=
      measurableSet_le measurable_const measurable_fst
    have hfA : IsBoxTensor ((ageAbove (Real.exp δ * T)).indicator f) :=
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.IsBoxTensor.indicator hf hA
    have hGz : zsum (inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) F) =ᵐ[ageμ p.c (-1 / 2)]
        (ageAbove (Real.exp δ * T)).indicator f := by
      filter_upwards [zsum_inRestr_ae hmZ hρ (ageAbove (Real.exp δ * T)) hA F, hFf] with x h1 h2
      rw [h1, h2]
      by_cases hx : x ∈ ageAbove (Real.exp δ * T)
      · simp [ind, Set.indicator_of_mem hx]
      · simp [ind, Set.indicator_of_notMem hx]
    have hSeps := hK p.ν p.ε p.c p.period p.ν_pos p.ε_pos p.c_pos rfl μ
      (by linarith) mZ ρb Seps' Seps hstress htrans _ _ hfA hGz
    have hSf := (isFarMask_iff p.R p.ν μ δ S Sf).1 hfar _ _ hfA hGz
    have hBelow : MeasurableSet (ageBelow T) := measurableSet_lt measurable_fst measurable_const
    have hf' : ∀ q : Chart, q.1 < Real.exp δ * T →
        (ageAbove (Real.exp δ * T)).indicator f q = 0 := by
      intro q hq
      exact Set.indicator_of_notMem (show q ∉ ageAbove (Real.exp δ * T) from fun h => not_le.2 hq h) f
    have hres : (outRestr p.c (ageBelow T) ((Seps - Sf) (inRestr p.c mZ ρb
        (ageAbove (Real.exp δ * T)) F)) : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)]
        (ageBelow T).indicator (fun _ => (1 : ℝ)) • ((Seps - Sf) (inRestr p.c mZ ρb
          (ageAbove (Real.exp δ * T)) F) : Chart → Merid) :=
      restrLp_ae hBelow _
    have hzero : ((outRestr p.c (ageBelow T) ∘L (Seps - Sf) ∘L
        inRestr p.c mZ ρb (ageAbove (Real.exp δ * T))) F : Chart → Merid) =ᵐ[ageμ p.c (-3 / 2)]
        (0 : Chart → Merid) := by
      simp only [ContinuousLinearMap.comp_apply]
      filter_upwards [hres, hSeps, hSf, Lp.coeFn_sub
        (Seps (inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) F))
        (Sf (inRestr p.c mZ ρb (ageAbove (Real.exp δ * T)) F))] with x h1 h2 h3 h4
      rw [h1]
      simp only [Pi.zero_apply]
      change (ageBelow T).indicator (fun _ => (1 : ℝ)) x • ((Seps - Sf) (inRestr p.c mZ ρb
          (ageAbove (Real.exp δ * T)) F) : Chart → Merid) x = 0
      by_cases hx : x ∈ ageBelow T
      · have hxT : x.1 < T := hx
        rw [Set.indicator_of_mem hx, one_smul, ContinuousLinearMap.sub_apply, h4, Pi.sub_apply,
          h2, h3, farOut_eq_fullOut_of_lt (R := p.R) hδ hTS _ hf' x hxT]
        exact sub_eq_zero.mpr rfl
      · rw [Set.indicator_of_notMem hx, zero_smul]
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    simp
  exact norm_le_zero_iff.1 hX

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
