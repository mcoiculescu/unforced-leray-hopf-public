import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1

/-!
# Part II-b, task `PartII-b:G4/3/6/1/7`: band velocity jets `RawVelBandJets`

Source of record: `the November 2 reference manuscript` 468-478 (`sct:fixed-band`).
Proof: on `s > 0` the train velocity is `v = (v - Vc) + Vc`.  The age jets are additive for jointly
smooth families (`vb_ageJet_sub`, from the slice formula `vb_slice_iteratedDeriv_eq`), so the four
jets of `v` are bounded by the `FixedBandJets` bound for `v - Vc` plus the `VcJetSup` bound for `Vc`.
The constant `Cp` is not used: the bounds are uniform in `η`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartI

/-- Slice formula: the `n`-th age derivative of `r ↦ K (r, w)` at `s > 0` is the `n`-th Fréchet
derivative of the jointly smooth `K` at `(s, w)` along the age direction `(1, 0)`. -/
theorem vb_slice_iteratedDeriv_eq {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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

/-- The `n`-th age derivative of the slice `w ↦ iteratedDeriv n (K (·, w)) s` is smooth in `w`,
for `s > 0`, of any order `m`. -/
theorem vb_slice_contDiffAt {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℝ × V → E) (hK : ContDiffOn ℝ ∞ K (Ioi 0 ×ˢ univ)) (n m : ℕ) {s : ℝ} (hs : 0 < s)
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
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => ℝ × V) E (fun _ => (1, 0))).contDiff.contDiffAt).comp
      w h2
  have heq : (fun w' : V => iteratedDeriv n (fun r => K (r, w')) s) =
      fun w' => iteratedFDeriv ℝ n K (s, w') (fun _ => (1, 0)) :=
    funext fun w' => vb_slice_iteratedDeriv_eq K hK n hs w'
  rw [heq]
  exact h3

/-- Slices of a jointly smooth family are smooth in the age variable at `s > 0`. -/
theorem vb_slice_smooth_at {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ → V → E) (hH : ContDiffOn ℝ ∞ (fun x : ℝ × V => H x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (v : V) (m : ℕ) : ContDiffAt ℝ m (fun r => H r v) s := by
  have h0 : ContDiffAt ℝ ∞ (fun x : ℝ × V => H x.1 x.2) (s, v) :=
    hH.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hs, trivial⟩)
  exact ContDiffAt.of_le (m := (m : WithTop ℕ∞)) (h0.comp s (contDiffAt_id.prodMk contDiffAt_const))
    (mod_cast le_top)

/-- Linearity of the age/space jet over a difference of jointly smooth families, at `s > 0`. -/
theorem vb_ageJet_sub (F G : ℝ → UnforcedLeray.Cyl.Plane → UnforcedLeray.Train.Vec)
    (hF : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => F x.1 x.2) (Ioi 0 ×ˢ univ))
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => G x.1 x.2) (Ioi 0 ×ˢ univ))
    {s : ℝ} (hs : 0 < s) (ℓ j : ℕ) (w : UnforcedLeray.Cyl.Plane) :
    ageJet ℓ j (fun r v => F r v - G r v) s w =
      ageJet ℓ j F s w - ageJet ℓ j G s w := by
  have hsub : ∀ v : UnforcedLeray.Cyl.Plane, iteratedDeriv ℓ (fun r => F r v - G r v) s =
      iteratedDeriv ℓ (fun r => F r v) s - iteratedDeriv ℓ (fun r => G r v) s := by
    intro v
    exact iteratedDeriv_sub (vb_slice_smooth_at F hF hs v ℓ) (vb_slice_smooth_at G hG hs v ℓ)
  have hjet : (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => F r v - G r v) s) =
      (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => F r v) s) -
        (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => G r v) s) :=
    funext hsub
  have hA : ContDiffAt ℝ j
      (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => F r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × UnforcedLeray.Cyl.Plane => F x.1 x.2) hF ℓ j hs w
  have hB : ContDiffAt ℝ j
      (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => G r v) s) w :=
    vb_slice_contDiffAt (fun x : ℝ × UnforcedLeray.Cyl.Plane => G x.1 x.2) hG ℓ j hs w
  unfold ageJet UnforcedLeray.Train.jet
  show iteratedFDeriv ℝ j
      (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => F r v - G r v) s) w =
    iteratedFDeriv ℝ j (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => F r v) s) w -
      iteratedFDeriv ℝ j (fun v : UnforcedLeray.Cyl.Plane => iteratedDeriv ℓ (fun r => G r v) s) w
  rw [hjet, iteratedFDeriv_sub_apply hA hB]

/-- `trainPeriod 2 ν = (ν²)⁻¹`. -/
theorem vb_trainPeriod_two {ν : ℝ} (hν : 0 < ν) :
    UnforcedLeray.Short.PartI.trainPeriod 2 ν = (ν ^ 2)⁻¹ := by
  unfold UnforcedLeray.Short.PartI.trainPeriod
  rw [Real.rpow_neg hν.le, Real.rpow_two]

/-- Transport of a BUC train along an equality of periods (only the velocity is kept). -/
theorem vb_transport {ν c c' : ℝ} (h : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hb : UnforcedLeray.Short.PartI.IsBUCTrain tr) :
    ∃ tr' : UnforcedLeray.B0140.TrainSol ν c',
      UnforcedLeray.Short.PartI.IsBUCTrain tr' ∧ tr'.v = tr.v := by
  subst h
  exact ⟨tr, hb, rfl⟩

/-- Exponent monotonicity of `ν ↦ (ν^a)⁻¹` on `(0, 1]`. -/
theorem vb_inv_pow_mono {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    (ν ^ a)⁻¹ ≤ (ν ^ b)⁻¹ :=
  inv_anti₀ (pow_pos hν b) (pow_le_pow_of_le_one hν.le hν1 hab)

/-- One band point: the jets of `v` at `(s, z)` with `s ≤ Σ/ν`, from the fixed-band and sup bounds
for `v - Vc` and `Vc`. -/
theorem vb_single (hS : UnforcedLeray.Short.IIb.TrainVelSmooth)
    (hV : UnforcedLeray.Short.IIb.VcSmooth) {Sig : ℝ} (ℓ j : ℕ) {ν₀ : ℝ}
    (_hν₀ : 0 < ν₀) (hν₀1 : ν₀ ≤ 1) {C D : ℝ} {N M K : ℕ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hN : N ≤ K) (hM : M ≤ K)
    (hF : ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod 2 ν), IsBUCTrain tr →
      ∀ s : ℝ, 0 < s → s ≤ Sig / ν → ∀ z : UnforcedLeray.Cyl.Plane,
        ‖ageJet ℓ j (fun r w => tr.v r w - Train.Vc ν (trainPeriod 2 ν) r w) s z‖ ≤
          C * (ν ^ N)⁻¹)
    (hJ : ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ s : ℝ, 0 < s → s ≤ Sig / ν → ∀ z : UnforcedLeray.Cyl.Plane,
      ‖ageJet ℓ j (fun r w => Train.Vc ν ((ν ^ 2)⁻¹) r w) s z‖ ≤ D * (ν ^ M)⁻¹)
    (p : Params) (d dm dp : ℝ) (hd : BgRegime p d dm dp) (hνp : p.ν ≤ ν₀)
    (hS' : p.ageCut = Sig) (s : ℝ) (hs : 0 < s) (hsH : s ≤ p.H) (z : UnforcedLeray.Cyl.Plane) :
    ‖ageJet ℓ j p.train.v s z‖ ≤ (C + D) * (p.ν ^ K)⁻¹ := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hνp.trans hν₀1
  have hsSig : s ≤ Sig / p.ν := by
    have hHdef : p.H = p.ageCut / p.ν := rfl
    rw [← hS']
    rw [hHdef] at hsH
    exact hsH
  have hc2 : trainPeriod 2 p.ν = (p.ν ^ 2)⁻¹ := vb_trainPeriod_two hνpos
  obtain ⟨tr', hbuc, hv⟩ :=
    vb_transport (hd.c_eq.trans hc2.symm) p.train hd.train_buc
  have hcpos : 0 < trainPeriod 2 p.ν := by rw [hc2]; positivity
  have hsmoothF : ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => p.train.v x.1 x.2)
      (Ioi 0 ×ˢ univ) := hS p d dm dp hd
  have hsmoothG : ContDiffOn ℝ ∞
      (fun x : ℝ × UnforcedLeray.Cyl.Plane => Train.Vc p.ν (trainPeriod 2 p.ν) x.1 x.2)
      (Ioi 0 ×ˢ univ) := hV p.ν (trainPeriod 2 p.ν) hνpos hcpos
  have key : ageJet ℓ j p.train.v s z =
      ageJet ℓ j (fun r w => p.train.v r w - Train.Vc p.ν (trainPeriod 2 p.ν) r w) s z +
        ageJet ℓ j (fun r w => Train.Vc p.ν (trainPeriod 2 p.ν) r w) s z := by
    have h := vb_ageJet_sub p.train.v (fun r w => Train.Vc p.ν (trainPeriod 2 p.ν) r w)
      hsmoothF hsmoothG hs ℓ j z
    rw [h]
    abel
  have hX := hF p.ν hνpos hνp tr' hbuc s hs hsSig z
  rw [hv] at hX
  have hY := hJ p.ν hνpos hνp s hs hsSig z
  rw [← hc2] at hY
  have hmN : (p.ν ^ N)⁻¹ ≤ (p.ν ^ K)⁻¹ := vb_inv_pow_mono hνpos hν1 hN
  have hmM : (p.ν ^ M)⁻¹ ≤ (p.ν ^ K)⁻¹ := vb_inv_pow_mono hνpos hν1 hM
  have hX' : ‖ageJet ℓ j (fun r w => p.train.v r w - Train.Vc p.ν (trainPeriod 2 p.ν) r w) s z‖ ≤
      C * (p.ν ^ K)⁻¹ :=
    hX.trans (mul_le_mul_of_nonneg_left hmN hC)
  have hY' : ‖ageJet ℓ j (fun r w => Train.Vc p.ν (trainPeriod 2 p.ν) r w) s z‖ ≤
      D * (p.ν ^ K)⁻¹ :=
    hY.trans (mul_le_mul_of_nonneg_left hmM hD)
  rw [key]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- **Band region** (SP 468-478): the four jets of `v` on `0 < s ≤ Σ/ν`, uniformly in `η`, from
`VcSmooth`, `TrainVelSmooth`, `VcJetSup` and `FixedBandJets`. -/
theorem rawVelBandJets_of (hS : UnforcedLeray.Short.IIb.TrainVelSmooth)
    (hV : UnforcedLeray.Short.IIb.VcSmooth) (hJ : UnforcedLeray.Short.IIb.VcJetSup)
    (hF : UnforcedLeray.Short.IIb.FixedBandJets) :
    UnforcedLeray.Short.IIb.RawVelBandJets := by
  intro Cp hCp Sig hSig dm dp hdm
  obtain ⟨C₁, N₁, ν₁, hC₁, hν₁, H₁⟩ := hF Sig hSig 0 0
  obtain ⟨C₂, N₂, ν₂, hC₂, hν₂, H₂⟩ := hF Sig hSig 1 0
  obtain ⟨C₃, N₃, ν₃, hC₃, hν₃, H₃⟩ := hF Sig hSig 0 1
  obtain ⟨C₄, N₄, ν₄, hC₄, hν₄, H₄⟩ := hF Sig hSig 2 0
  obtain ⟨D₁, M₁, μ₁, hD₁, hμ₁, G₁⟩ := hJ Sig hSig 0 0
  obtain ⟨D₂, M₂, μ₂, hD₂, hμ₂, G₂⟩ := hJ Sig hSig 1 0
  obtain ⟨D₃, M₃, μ₃, hD₃, hμ₃, G₃⟩ := hJ Sig hSig 0 1
  obtain ⟨D₄, M₄, μ₄, hD₄, hμ₄, G₄⟩ := hJ Sig hSig 2 0
  set ν₀ : ℝ := min (min (min (min ν₁ ν₂) (min ν₃ ν₄)) (min (min μ₁ μ₂) (min μ₃ μ₄))) 1
    with hν₀def
  have hν₀pos : 0 < ν₀ := by
    rw [hν₀def]
    refine lt_min (lt_min (lt_min (lt_min hν₁ hν₂) (lt_min hν₃ hν₄))
      (lt_min (lt_min hμ₁ hμ₂) (lt_min hμ₃ hμ₄))) one_pos
  have hν₀1 : ν₀ ≤ 1 := min_le_right _ _
  have hle₁ : ν₀ ≤ ν₁ := by simp [hν₀def, min_le_iff]
  have hle₂ : ν₀ ≤ ν₂ := by simp [hν₀def, min_le_iff]
  have hle₃ : ν₀ ≤ ν₃ := by simp [hν₀def, min_le_iff]
  have hle₄ : ν₀ ≤ ν₄ := by simp [hν₀def, min_le_iff]
  have hleμ₁ : ν₀ ≤ μ₁ := by simp [hν₀def, min_le_iff]
  have hleμ₂ : ν₀ ≤ μ₂ := by simp [hν₀def, min_le_iff]
  have hleμ₃ : ν₀ ≤ μ₃ := by simp [hν₀def, min_le_iff]
  have hleμ₄ : ν₀ ≤ μ₄ := by simp [hν₀def, min_le_iff]
  refine ⟨(C₁ + D₁) + (C₂ + D₂) + (C₃ + D₃) + (C₄ + D₄),
    N₁ + N₂ + N₃ + N₄ + M₁ + M₂ + M₃ + M₄, ν₀,
    by linarith, hν₀pos, ?_⟩
  intro p d hd hν hS' x hx0 hxH _hη
  have hsH : x.1 ≤ p.H := hxH
  have e₁ := vb_single (K := N₁ + N₂ + N₃ + N₄ + M₁ + M₂ + M₃ + M₄) hS hV 0 0 hν₀pos hν₀1 hC₁.le hD₁.le
    (by omega) (by omega)
    (fun ν hν0 hνle tr htr s hs hsS z => H₁ ν hν0 (hνle.trans hle₁) tr htr s hs hsS z)
    (fun ν hν0 hνle s hs hsS z => G₁ ν hν0 (hνle.trans hleμ₁) s hs hsS z)
    p d dm dp hd hν hS' x.1 hx0 hsH x.2
  have e₂ := vb_single (K := N₁ + N₂ + N₃ + N₄ + M₁ + M₂ + M₃ + M₄) hS hV 1 0 hν₀pos hν₀1 hC₂.le hD₂.le
    (by omega) (by omega)
    (fun ν hν0 hνle tr htr s hs hsS z => H₂ ν hν0 (hνle.trans hle₂) tr htr s hs hsS z)
    (fun ν hν0 hνle s hs hsS z => G₂ ν hν0 (hνle.trans hleμ₂) s hs hsS z)
    p d dm dp hd hν hS' x.1 hx0 hsH x.2
  have e₃ := vb_single (K := N₁ + N₂ + N₃ + N₄ + M₁ + M₂ + M₃ + M₄) hS hV 0 1 hν₀pos hν₀1 hC₃.le hD₃.le
    (by omega) (by omega)
    (fun ν hν0 hνle tr htr s hs hsS z => H₃ ν hν0 (hνle.trans hle₃) tr htr s hs hsS z)
    (fun ν hν0 hνle s hs hsS z => G₃ ν hν0 (hνle.trans hleμ₃) s hs hsS z)
    p d dm dp hd hν hS' x.1 hx0 hsH x.2
  have e₄ := vb_single (K := N₁ + N₂ + N₃ + N₄ + M₁ + M₂ + M₃ + M₄) hS hV 2 0 hν₀pos hν₀1 hC₄.le hD₄.le
    (by omega) (by omega)
    (fun ν hν0 hνle tr htr s hs hsS z => H₄ ν hν0 (hνle.trans hle₄) tr htr s hs hsS z)
    (fun ν hν0 hνle s hs hsS z => G₄ ν hν0 (hνle.trans hleμ₄) s hs hsS z)
    p d dm dp hd hν hS' x.1 hx0 hsH x.2
  linarith [e₁, e₂, e₃, e₄]

end UnforcedLeray.Short.IIb
