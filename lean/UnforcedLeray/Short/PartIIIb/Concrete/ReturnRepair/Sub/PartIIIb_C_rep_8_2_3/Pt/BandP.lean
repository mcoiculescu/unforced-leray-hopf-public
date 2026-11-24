import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/17`: the band pressure jets `BandP`

Source of record: `the November 2 reference manuscript` 5484-5492 (`p = (p - p_c^p) + p_c^p`)
and 468-478.  Write `F = tr.p - pc`.  The age jet of `tr.p` splits (scalar linearity of `ageJet` over
the difference of two jointly smooth families, `pcAgeJetSub`) as `∂_s^ℓ D^{m+1} F + ∂_s^ℓ D^{m+1} p_c^p`.
The first term is `GradJetShift` (`≤ 2‖∂_s^ℓ D^m ∇F‖`) and `FixedBandP` bounds `∇F`; the second is
`PcJetSup`.  The constants merge by `ν⁻¹ ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- Slice formula: the `n`-th age derivative of `r ↦ K (r, w)` at `s > 0` is the `n`-th Fréchet
derivative of the jointly smooth `K` at `(s, w)` along the age direction `(1, 0)`. -/
theorem pcSliceIterEq {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℝ × V → E) (hK : ContDiffOn ℝ ∞ K (Ioi 0 ×ˢ univ)) (n : ℕ) {s : ℝ} (hs : 0 < s) (w : V) :
    iteratedDeriv n (fun r => K (r, w)) s = iteratedFDeriv ℝ n K (s, w) (fun _ => (1, 0)) := by
  have hopen : IsOpen {p : ℝ × V | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hmaps : MapsTo (fun p : ℝ × V => p + ((0 : ℝ), w)) {p : ℝ × V | 0 < p.1}
      (Ioi 0 ×ˢ (univ : Set V)) :=
    fun p hp => ⟨by simpa using hp, Set.mem_univ _⟩
  have hsmooth : ContDiffOn ℝ ∞ (fun p : ℝ × V => K (p + ((0 : ℝ), w))) {p : ℝ × V | 0 < p.1} :=
    hK.comp (contDiff_id.add contDiff_const).contDiffOn hmaps
  have hfun : (fun r : ℝ => K (r, w)) =
      (fun p : ℝ × V => K (p + ((0 : ℝ), w))) ∘ (ContinuousLinearMap.inl ℝ ℝ V) := by
    funext r
    simp
  have hL : ContinuousLinearMap.inl ℝ ℝ V s ∈ {p : ℝ × V | 0 < p.1} := by simpa using hs
  have hpre : IsOpen ((ContinuousLinearMap.inl ℝ ℝ V) ⁻¹' {p : ℝ × V | 0 < p.1}) :=
    hopen.preimage (ContinuousLinearMap.continuous _)
  have hs_pre : s ∈ (ContinuousLinearMap.inl ℝ ℝ V) ⁻¹' {p : ℝ × V | 0 < p.1} := hL
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    (ContinuousLinearMap.inl ℝ ℝ V) hsmooth hopen.uniqueDiffOn hpre.uniqueDiffOn hL
    (i := n) (mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hopen hL,
    iteratedFDerivWithin_of_isOpen n hpre hs_pre] at hcomp
  have hA : iteratedFDeriv ℝ n (fun p : ℝ × V => K (p + ((0 : ℝ), w)))
      (ContinuousLinearMap.inl ℝ ℝ V s) = iteratedFDeriv ℝ n K (s, w) := by
    simp [iteratedFDeriv_comp_add_right]
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, hcomp, hA]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1

/-- Slices of a jointly smooth family are smooth in the age variable at `s > 0`. -/
theorem pcSliceSmooth (H : ℝ → Plane → ℝ)
    (hH : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => H x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (v : Plane) (m : ℕ) : ContDiffAt ℝ m (fun r => H r v) s := by
  have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × Plane => H x.1 x.2) (s, v) :=
    hH.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  exact ContDiffAt.of_le (m := (m : WithTop ℕ∞)) (h0.comp s (contDiffAt_id.prodMk contDiffAt_const))
    (mod_cast le_top)

/-- The `ℓ`-th age derivative of the slice `w ↦ ∂_s^ℓ K(s, w)` is smooth in `w`, of any order `m`. -/
theorem pcSliceContDiffAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ℝ × V → ℝ) (hK : ContDiffOn ℝ ∞ K (Ioi 0 ×ˢ univ)) (n m : ℕ) {s : ℝ} (hs : 0 < s)
    (w : V) :
    ContDiffAt ℝ m (fun w' : V => iteratedDeriv n (fun r => K (r, w')) s) w := by
  have hKa : ContDiffAt ℝ ∞ K (s, w) :=
    hK.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  have h1 : ContDiffAt ℝ m (iteratedFDeriv ℝ n K) (s, w) :=
    hKa.iteratedFDeriv_right (m := (m : WithTop ℕ∞)) (i := n) (mod_cast le_top)
  have h2 : ContDiffAt ℝ m (fun w' : V => iteratedFDeriv ℝ n K (s, w')) w :=
    h1.comp w (contDiffAt_const.prodMk contDiffAt_id)
  have h3 : ContDiffAt ℝ m
      (fun w' : V => iteratedFDeriv ℝ n K (s, w') (fun _ => (1, 0))) w :=
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × V) ℝ (fun _ => (1, 0))).contDiff.contDiffAt).comp
      w h2
  have heq : (fun w' : V => iteratedDeriv n (fun r => K (r, w')) s) =
      fun w' => iteratedFDeriv ℝ n K (s, w') (fun _ => (1, 0)) :=
    funext fun w' => pcSliceIterEq K hK n hs w'
  rw [heq]
  exact h3

/-- Scalar linearity of the age/space jet over a difference of jointly smooth families, at `s > 0`
(the `ℝ`-valued copy of `IIb.vb_ageJet_sub`). -/
theorem pcAgeJetSub (F G : ℝ → Plane → ℝ)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (w : Plane) :
    UnforcedLeray.Short.PartI.ageJet ℓ j (fun r v => F r v - G r v) s w =
      UnforcedLeray.Short.PartI.ageJet ℓ j F s w - UnforcedLeray.Short.PartI.ageJet ℓ j G s w := by
  have hsub : ∀ v : Plane, iteratedDeriv ℓ (fun r => F r v - G r v) s =
      iteratedDeriv ℓ (fun r => F r v) s - iteratedDeriv ℓ (fun r => G r v) s := by
    intro v
    exact iteratedDeriv_sub (pcSliceSmooth F hF hs v ℓ) (pcSliceSmooth G hG hs v ℓ)
  have hjet : (fun v : Plane => iteratedDeriv ℓ (fun r => F r v - G r v) s) =
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) -
        (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) :=
    funext hsub
  have hA : ContDiffAt ℝ j
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) w :=
    pcSliceContDiffAt (fun x : ℝ × Plane => F x.1 x.2) hF ℓ j hs w
  have hB : ContDiffAt ℝ j
      (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) w :=
    pcSliceContDiffAt (fun x : ℝ × Plane => G x.1 x.2) hG ℓ j hs w
  unfold UnforcedLeray.Short.PartI.ageJet UnforcedLeray.Train.jet
  show iteratedFDeriv ℝ j
      (fun v : Plane => iteratedDeriv ℓ (fun r => F r v - G r v) s) w =
    iteratedFDeriv ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => F r v) s) w -
      iteratedFDeriv ℝ j (fun v : Plane => iteratedDeriv ℓ (fun r => G r v) s) w
  rw [hjet, iteratedFDeriv_sub_apply hA hB]

theorem bandP_of (h1 : FixedBandP) (h2 : PcSmooth) (h3 : PcJetSup) (h4 : GradJetShift) : BandP := by
  intro ℓ m
  obtain ⟨C₁, k₁, a₁, ha₁, H₁⟩ := h1 ℓ m
  obtain ⟨C₂, k₂, a₂, ha₂, H₂⟩ := h3 ℓ (m + 1)
  refine ⟨2 * |C₁| + |C₂|, k₁ + k₂, min (min a₁ a₂) 1, lt_min (lt_min ha₁ ha₂) one_pos, ?_⟩
  intro ν hν hνa tr hbuc s hs hsν z
  have hνm : ν ≤ min a₁ a₂ := (le_min_iff.1 hνa).1
  have hνa₁ : ν ≤ a₁ := (le_min_iff.1 hνm).1
  have hνa₂ : ν ≤ a₂ := (le_min_iff.1 hνm).2
  have hν1 : ν ≤ 1 := (le_min_iff.1 hνa).2
  have hc : (1 : ℝ) ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hcpos : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hcν : 0 < cOf ν := by
    unfold cOf
    exact inv_pos.2 (pow_pos hν 2)
  have hTp : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.p x.1 x.2) (Ioi 0 ×ˢ univ) :=
    tr.isTrain.smooth_p.mono (Set.prod_mono Ioi_subset_Ici_self subset_rfl)
  have hPc : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => UnforcedLeray.Train.pc ν (cOf ν) x.1 x.2)
      (Ioi 0 ×ˢ univ) := h2 ν (cOf ν) hν hcν
  have hFs : ContDiffOn ℝ ∞
      (fun x : ℝ × Plane => (fun r v => tr.p r v - UnforcedLeray.Train.pc ν (cOf ν) r v) x.1 x.2)
      (Ioi 0 ×ˢ univ) := hTp.sub hPc
  have hlin := pcAgeJetSub tr.p (fun r v => UnforcedLeray.Train.pc ν (cOf ν) r v) hTp hPc hs
    ℓ (m + 1) z
  have hsplit : UnforcedLeray.Short.PartI.ageJet ℓ (m + 1) tr.p s z =
      UnforcedLeray.Short.PartI.ageJet ℓ (m + 1)
          (fun r v => tr.p r v - UnforcedLeray.Train.pc ν (cOf ν) r v) s z +
        UnforcedLeray.Short.PartI.ageJet ℓ (m + 1)
          (fun r v => UnforcedLeray.Train.pc ν (cOf ν) r v) s z := by
    rw [hlin, sub_add_cancel]
  have hb1 := h4 (fun r v => tr.p r v - UnforcedLeray.Train.pc ν (cOf ν) r v) hFs ℓ m s hs z
  have hb2 := H₁ ν hν hνa₁ tr hbuc s hs hsν z
  have hb3 := H₂ ν hν hνa₂ s hs hsν z
  have hpow : ν⁻¹ ^ k₁ ≤ ν⁻¹ ^ (k₁ + k₂) := pow_le_pow_right₀ hc (Nat.le_add_right k₁ k₂)
  have hpow2 : ν⁻¹ ^ k₂ ≤ ν⁻¹ ^ (k₁ + k₂) := pow_le_pow_right₀ hc (Nat.le_add_left k₂ k₁)
  have eA : C₁ * ν⁻¹ ^ k₁ ≤ |C₁| * ν⁻¹ ^ (k₁ + k₂) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₁) (pow_nonneg hcpos _)).trans
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg C₁))
  have eB : C₂ * ν⁻¹ ^ k₂ ≤ |C₂| * ν⁻¹ ^ (k₁ + k₂) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₂) (pow_nonneg hcpos _)).trans
      (mul_le_mul_of_nonneg_left hpow2 (abs_nonneg C₂))
  have hid : (2 * |C₁| + |C₂|) * ν⁻¹ ^ (k₁ + k₂) =
      2 * (|C₁| * ν⁻¹ ^ (k₁ + k₂)) + |C₂| * ν⁻¹ ^ (k₁ + k₂) := by ring
  have htri : ‖UnforcedLeray.Short.PartI.ageJet ℓ (m + 1) tr.p s z‖ ≤
      ‖UnforcedLeray.Short.PartI.ageJet ℓ (m + 1)
          (fun r v => tr.p r v - UnforcedLeray.Train.pc ν (cOf ν) r v) s z‖ +
        ‖UnforcedLeray.Short.PartI.ageJet ℓ (m + 1)
          (fun r v => UnforcedLeray.Train.pc ν (cOf ν) r v) s z‖ := by
    rw [hsplit]
    exact norm_add_le _ _
  rw [hid]
  linarith [htri, hb1, hb2, hb3, eA, eB]

end UnforcedLeray.Short.PartIIIb.Concrete
