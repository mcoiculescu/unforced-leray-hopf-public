import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc.Assembly

/-!
# `PartIII-a:T21/c3/2/1/2/2/2/1`: local dense continuity `RelB4loc` of the pinned relative free evolution

Source: `the November 2 reference manuscript` lines 2941-2970
(`\overline F(z,t) = I_z F(z,t) R_t + S(z,t)(I - Π_t)`, `S f(y) = ρ⁴ f(ρ y)`, `ρ = d(t)/d(z)`).

Fix `p₀ = (τ₀, σ₀)` in the block triangle, with start age `s₀ = ageAt ν t₁ σ₀` and cell length
`d₀ = d(s₀)`.  The dense set is `denseClass m d₀`: smooth compactly supported fields vanishing near the
lines `|Re z| = d₀/2` (`dense_denseClass`).  Such a field splits as `W₁ + i W₂` with real `W₁, W₂` of
the same kind.  For a real field `Φ` and `(τ, σ)` near `p₀` the cell `d(s)` stays inside the region
where `Φ` has no mass across the cell boundary, so the cell restriction of `Φ`, rescaled by `J_{a_s}`,
is a cylinder test `f(s)` (`isCylTest_fData`), and the pinning gives
`F_rel(τ,σ) W = N(s,t)⁻¹ (J_{1/a_t} ⟦ω_s(t)⟧ + J_{(d_t/d_s)²} E)` (`ident_eq`), with `ω_s` the free
cylinder flow from `f(s)` at age `s` and `E` the fixed exterior part of `Φ`.  Each factor is
continuous at `p₀`: the clocks, the joint dilation (`tendsto_dilW'_joint`) and the free cylinder
flow in (start age, time) (`cyl_joint_tendsto`, restart + linearity + uniqueness).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.RelB4locAux

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsMildSub
open UnforcedLeray.Blueprint.Planar

/-- Continuity of `p ↦ F_rel p.1 p.2 W` within the block triangle at `p₀` for a real smooth
compactly supported field vanishing near the boundary lines of the cell `d(s₀)`. -/
theorem real_case {P : PlanarData} {m B ν t₁ t₂ : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hm : 8 < m) (hν : 0 < ν) (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂) (hBz : movingZ ν t₂ - movingZ ν t₁ = B)
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel)
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ blockTriangle B) {d₀ : ℝ}
    (hd₀ : d₀ = cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.2)))
    {Φr : ℂ → ℝ} (hΦs : ContDiff ℝ ∞ Φr) (hΦc : HasCompactSupport Φr) {δ : ℝ} (hδ : 0 < δ)
    (hv : ∀ z : ℂ, d₀ / 2 - δ < |z.re| → |z.re| < d₀ / 2 + δ → Φr z = 0)
    (W : Planar.L2w m) (hW : ⇑W =ᵐ[Planar.wMeasure m] fun z => ((Φr z : ℝ) : ℂ)) :
    ContinuousWithinAt (fun p : ℝ × ℝ => F_rel p.1 p.2 W) (blockTriangle B) p₀ := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hm1 : 1 < m := by linarith
  have hT : 0 ≤ t₂ := ht₁.trans ht₁₂
  obtain ⟨hσ₀, hστ₀, hτ₀⟩ := hp₀
  have hz : ∀ τ : ℝ, τ ≤ B → ν * (movingZ ν t₁ + τ) < 1 := by
    intro τ hτ
    have hlt : ν * movingZ ν t₂ < 1 := FrameStableSub.nu_mul_movingZ_lt_one hν hT
    have hle := mul_le_mul_of_nonneg_left
      (show movingZ ν t₁ + τ ≤ movingZ ν t₂ by linarith) hν.le
    linarith
  have hA : ∀ s : ℝ, 0 ≤ s → 0 < clockA ν s := fun s hs => by unfold clockA; positivity
  have hdpos : ∀ a : ℝ, 0 < a → 0 < cellLen (ν ^ (-2 : ℝ)) a :=
    fun a ha => div_pos hc (Real.sqrt_pos.2 ha)
  have hsA : ContinuousAt (fun p : ℝ × ℝ => ageAt ν t₁ p.2) p₀ :=
    (continuousAt_ageAt (hz p₀.2 (hστ₀.trans hτ₀))).comp continuous_snd.continuousAt
  have htA : ContinuousAt (fun p : ℝ × ℝ => ageAt ν t₁ p.1) p₀ :=
    (continuousAt_ageAt (hz p₀.1 hτ₀)).comp continuous_fst.continuousAt
  obtain ⟨hts₀, hst₀, ht₀₂⟩ := ageAt_props hν ht₁ ht₁₂ hBz hσ₀ hστ₀ hτ₀
  have hs₀ : 0 ≤ ageAt ν t₁ p₀.2 := ht₁.trans hts₀
  have ht₀ : 0 ≤ ageAt ν t₁ p₀.1 := hs₀.trans hst₀
  have ha₀ := hA _ hs₀
  have hat₀ := hA _ ht₀
  have hd₀' : |cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.2)) - d₀| < δ / 2 := by
    rw [hd₀, sub_self, abs_zero]; exact half_pos hδ
  -- the points near `p₀` where the cell `d(s)` does not cut the support of `Φ`
  have hnear : ∀ᶠ p in 𝓝 p₀,
      |cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.2)) - d₀| < δ / 2 := by
    have h := Metric.tendsto_nhds.1 (continuousAt_cellLen_comp (c := ν ^ (-2 : ℝ)) hsA ha₀)
      (δ / 2) (half_pos hδ)
    filter_upwards [h] with p hp
    rw [hd₀]
    simpa only [Real.dist_eq] using hp
  have hgood : ∀ᶠ p in 𝓝[blockTriangle B] p₀, p ∈ blockTriangle B ∧
      |cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.2)) - d₀| < δ / 2 :=
    Filter.Eventually.and eventually_mem_nhdsWithin (hnear.filter_mono nhdsWithin_le_nhds)
  -- the cylinder data and their free flows
  have hex : ∀ s : ℝ, ∃ R : ℝ → B0579.Plane → ℝ, 0 ≤ s →
      B0579.IsCylTest (ν ^ (-2 : ℝ)) (fData (ν ^ (-2 : ℝ)) Φr (clockA ν s)) →
        IIb.IsFreeCylFlow m tr s (fData (ν ^ (-2 : ℝ)) Φr (clockA ν s)) R := by
    intro s
    by_cases h : 0 ≤ s ∧ B0579.IsCylTest (ν ^ (-2 : ℝ)) (fData (ν ^ (-2 : ℝ)) Φr (clockA ν s))
    · obtain ⟨R, hR, -⟩ := exists_regular_of_test hm hν hc hbu h.1 h.2
      exact ⟨R, fun _ _ => hR⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Fl hFl using hex
  have hcyl₀ := isCylTest_fData hc ha₀ hδ hd₀' hΦs hΦc hv
  have hfl₀ := hFl _ hs₀ hcyl₀
  -- the exterior field
  have hΦL : MemLp (fun z => ((Φr z : ℝ) : ℂ)) 2 (Planar.wMeasure m) := (Lp.memLp W).ae_eq hW
  obtain ⟨E, hE⟩ : ∃ E : Planar.L2w m, ⇑E =ᵐ[Planar.wMeasure m] eFun d₀ Φr :=
    ⟨_, (memLp_eFun (d₀ := d₀) hΦL).coeFn_toLp⟩
  -- identification of the pinned value near `p₀`
  have hid : ∀ p : ℝ × ℝ, p ∈ blockTriangle B →
      |cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.2)) - d₀| < δ / 2 →
      F_rel p.1 p.2 W = ((clockN P ν (ageAt ν t₁ p.2) (ageAt ν t₁ p.1) : ℂ)⁻¹) •
        (dilW' hm1 (clockA ν (ageAt ν t₁ p.1))⁻¹
            (liftC (ν ^ (-2 : ℝ)) m (Fl (ageAt ν t₁ p.2) (ageAt ν t₁ p.1))) +
          dilW' hm1 ((cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.2)) /
            cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.1))) ^ 2)⁻¹ E) := by
    intro p hp hd
    obtain ⟨hσ, hστ, hτ⟩ := hp
    obtain ⟨hts, hst, -⟩ := ageAt_props hν ht₁ ht₁₂ hBz hσ hστ hτ
    have hs : 0 ≤ ageAt ν t₁ p.2 := ht₁.trans hts
    have has := hA _ hs
    have hat := hA _ (hs.trans hst)
    have hcyl := isCylTest_fData hc has hδ hd hΦs hΦc hv
    have hfl := hFl _ hs hcyl
    have hpin : ∀ᵐ z ∂volume,
        cToPlane z ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.2))) →
        (W : ℂ → ℂ) z = JscaleInv (clockA ν (ageAt ν t₁ p.2))
          (fun x => ((fData (ν ^ (-2 : ℝ)) Φr (clockA ν (ageAt ν t₁ p.2)) x : ℝ) : ℂ))
          (cToPlane z) := by
      filter_upwards [(Planar.volume_ac m).ae_le hW] with z hz hzc
      rw [JscaleInv_fData hc has Φr hzc, planeToC_cToPlane]
      exact hz
    have hV := hF p.2 p.1 hσ hστ hτ _ hcyl _ hfl W hpin
    exact ident_eq hm1 hc has hat hδ hd hv W hW _ (hfl.memX _ hst) E hE _ hV
  -- convergence of the free cylinder flows in (start age, time)
  have hpair : Tendsto (fun p : ℝ × ℝ => (ageAt ν t₁ p.2, ageAt ν t₁ p.1))
      (𝓝[blockTriangle B] p₀) (𝓝 (ageAt ν t₁ p₀.2, ageAt ν t₁ p₀.1)) :=
    (hsA.prodMk htA).tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ q in Filter.map (fun p : ℝ × ℝ => (ageAt ν t₁ p.2, ageAt ν t₁ p.1))
      (𝓝[blockTriangle B] p₀),
      0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ t₂ ∧
        B0579.IsCylTest (ν ^ (-2 : ℝ)) (fData (ν ^ (-2 : ℝ)) Φr (clockA ν q.1)) ∧
        IIb.IsFreeCylFlow m tr q.1 (fData (ν ^ (-2 : ℝ)) Φr (clockA ν q.1)) (Fl q.1) := by
    rw [Filter.eventually_map]
    filter_upwards [hgood] with p hp
    obtain ⟨⟨hσ, hστ, hτ⟩, hd⟩ := hp
    obtain ⟨hts, hst, ht2⟩ := ageAt_props hν ht₁ ht₁₂ hBz hσ hστ hτ
    have hs : 0 ≤ ageAt ν t₁ p.2 := ht₁.trans hts
    have hcyl := isCylTest_fData hc (hA _ hs) hδ hd hΦs hΦc hv
    exact ⟨hs, hst, ht2, hcyl, hFl _ hs hcyl⟩
  obtain ⟨η, hη, hηc, hvan⟩ := fData_vanish hc ha₀ hδ hd₀' hv
  have hfa : Tendsto (fun q : ℝ × ℝ => clockA ν q.1)
      (Filter.map (fun p : ℝ × ℝ => (ageAt ν t₁ p.2, ageAt ν t₁ p.1)) (𝓝[blockTriangle B] p₀))
      (𝓝 (clockA ν (ageAt ν t₁ p₀.2))) := by
    have hcont : Continuous (fun q : ℝ × ℝ => clockA ν q.1) := by
      unfold clockA; fun_prop
    exact (hcont.tendsto _).mono_left hpair
  have hfc : Tendsto (fun q : ℝ × ℝ => eLpNorm (fData (ν ^ (-2 : ℝ)) Φr (clockA ν q.1) -
      fData (ν ^ (-2 : ℝ)) Φr (clockA ν (ageAt ν t₁ p₀.2))) 2
        (B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
      (Filter.map (fun p : ℝ × ℝ => (ageAt ν t₁ p.2, ageAt ν t₁ p.1)) (𝓝[blockTriangle B] p₀))
      (𝓝 0) :=
    fData_tendsto hm1 hc W hW ha₀ hfa
      (hev.mono fun q hq => (hq.2.2.2.1.continuous.sub hcyl₀.continuous).aestronglyMeasurable)
  have hcj := cyl_joint_tendsto hm hν hc hbu hT
    (fun s => fData (ν ^ (-2 : ℝ)) Φr (clockA ν s)) Fl hs₀ hst₀ ht₀₂ hcyl₀ hfl₀ hη hηc hvan
    (Filter.map (fun p : ℝ × ℝ => (ageAt ν t₁ p.2, ageAt ν t₁ p.1)) (𝓝[blockTriangle B] p₀))
    hpair hev hfc
  have hlift : Tendsto
      (fun p : ℝ × ℝ => liftC (ν ^ (-2 : ℝ)) m (Fl (ageAt ν t₁ p.2) (ageAt ν t₁ p.1)))
      (𝓝[blockTriangle B] p₀)
      (𝓝 (liftC (ν ^ (-2 : ℝ)) m (Fl (ageAt ν t₁ p₀.2) (ageAt ν t₁ p₀.1)))) := by
    have h := tendsto_liftC (g := fun q : ℝ × ℝ => Fl q.1 q.2) (hfl₀.memX _ hst₀)
      (hev.mono fun q hq => hq.2.2.2.2.memX _ hq.2.1) hcj
    exact tendsto_map'_iff.1 h
  -- the clocks and the dilation parameters
  have hNt : Tendsto
      (fun p : ℝ × ℝ => ((clockN P ν (ageAt ν t₁ p.2) (ageAt ν t₁ p.1) : ℂ)⁻¹))
      (𝓝[blockTriangle B] p₀)
      (𝓝 ((clockN P ν (ageAt ν t₁ p₀.2) (ageAt ν t₁ p₀.1) : ℂ)⁻¹)) := by
    have hN := continuousAt_clockN_comp P hν hsA htA hs₀ ht₀
    have hN0 : ((clockN P ν (ageAt ν t₁ p₀.2) (ageAt ν t₁ p₀.1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (clockN_pos P hν hs₀ ht₀).ne'
    exact ((Complex.continuous_ofReal.continuousAt.comp hN).inv₀ hN0).tendsto.mono_left
      nhdsWithin_le_nhds
  have hAt : Tendsto (fun p : ℝ × ℝ => (clockA ν (ageAt ν t₁ p.1))⁻¹) (𝓝[blockTriangle B] p₀)
      (𝓝 (clockA ν (ageAt ν t₁ p₀.1))⁻¹) := by
    have h : ContinuousAt (fun p : ℝ × ℝ => clockA ν (ageAt ν t₁ p.1)) p₀ := by
      unfold clockA; exact continuousAt_const.add (continuousAt_const.mul htA)
    exact (h.inv₀ hat₀.ne').tendsto.mono_left nhdsWithin_le_nhds
  have hRat : Tendsto (fun p : ℝ × ℝ => ((cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.2)) /
      cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p.1))) ^ 2)⁻¹) (𝓝[blockTriangle B] p₀)
      (𝓝 ((cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.2)) /
        cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.1))) ^ 2)⁻¹) := by
    have hds := continuousAt_cellLen_comp (c := ν ^ (-2 : ℝ)) hsA ha₀
    have hdt := continuousAt_cellLen_comp (c := ν ^ (-2 : ℝ)) htA hat₀
    exact (((hds.div hdt (hdpos _ hat₀).ne').pow 2).inv₀
      (pow_ne_zero 2 (div_ne_zero (hdpos _ ha₀).ne' (hdpos _ hat₀).ne'))).tendsto.mono_left
      nhdsWithin_le_nhds
  have hβ₀ : 0 < ((cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.2)) /
      cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.1))) ^ 2)⁻¹ :=
    inv_pos.2 (pow_pos (div_pos (hdpos _ ha₀) (hdpos _ hat₀)) 2)
  have h1 := tendsto_dilW'_joint hm1 (inv_pos.2 hat₀) hAt hlift
  have h2 := tendsto_dilW'_joint hm1 hβ₀ hRat
    (tendsto_const_nhds : Tendsto (fun _ : ℝ × ℝ => E) (𝓝[blockTriangle B] p₀) (𝓝 E))
  have hG := hNt.smul (h1.add h2)
  have hid₀ := hid p₀ ⟨hσ₀, hστ₀, hτ₀⟩ hd₀'
  show Tendsto (fun p : ℝ × ℝ => F_rel p.1 p.2 W) (𝓝[blockTriangle B] p₀) (𝓝 (F_rel p₀.1 p₀.2 W))
  rw [hid₀]
  refine hG.congr' ?_
  filter_upwards [hgood] with p hp
  exact (hid p hp.1 hp.2).symm

/-- Continuity on the dense class: split a complex field into its real and imaginary parts. -/
theorem complex_case {P : PlanarData} {m B ν t₁ t₂ : ℝ}
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    (hm : 8 < m) (hν : 0 < ν) (hbu : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    (ht₁ : 0 ≤ t₁) (ht₁₂ : t₁ ≤ t₂) (hBz : movingZ ν t₂ - movingZ ν t₁ = B)
    {F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m}
    (hF : IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel)
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ blockTriangle B) {d₀ : ℝ}
    (hd₀ : d₀ = cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.2)))
    {W : Planar.L2w m} (hWD : W ∈ denseClass m d₀) :
    ContinuousWithinAt (fun p : ℝ × ℝ => F_rel p.1 p.2 W) (blockTriangle B) p₀ := by
  obtain ⟨Φ, hΦs, hΦc, ⟨δ, hδ, hv⟩, hW⟩ := hWD
  have hMΦ : MemLp Φ 2 (Planar.wMeasure m) := (Lp.memLp W).ae_eq hW
  have hΦcont : Continuous Φ := hΦs.continuous
  have hMr : MemLp (fun z => (((Φ z).re : ℝ) : ℂ)) 2 (Planar.wMeasure m) :=
    hMΦ.of_le
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hΦcont)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have hMi : MemLp (fun z => (((Φ z).im : ℝ) : ℂ)) 2 (Planar.wMeasure m) :=
    hMΦ.of_le
      (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hΦcont)).aestronglyMeasurable
      (Eventually.of_forall fun z => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : Planar.L2w m,
      ⇑W₁ =ᵐ[Planar.wMeasure m] fun z => (((Φ z).re : ℝ) : ℂ) := ⟨_, hMr.coeFn_toLp⟩
  obtain ⟨W₂, hW₂⟩ : ∃ W₂ : Planar.L2w m,
      ⇑W₂ =ᵐ[Planar.wMeasure m] fun z => (((Φ z).im : ℝ) : ℂ) := ⟨_, hMi.coeFn_toLp⟩
  have hsplit : W = W₁ + Complex.I • W₂ := by
    apply Lp.ext
    filter_upwards [hW, Lp.coeFn_add W₁ (Complex.I • W₂), Lp.coeFn_smul Complex.I W₂, hW₁, hW₂]
      with z h0 h1 h2 h3 h4
    rw [h0, h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul, mul_comm]
    exact (Complex.re_add_im (Φ z)).symm
  have hre : ContDiff ℝ ∞ (fun z => (Φ z).re) := Complex.reCLM.contDiff.comp hΦs
  have him : ContDiff ℝ ∞ (fun z => (Φ z).im) := Complex.imCLM.contDiff.comp hΦs
  have hrec : HasCompactSupport (fun z => (Φ z).re) := hΦc.comp_left Complex.zero_re
  have himc : HasCompactSupport (fun z => (Φ z).im) := hΦc.comp_left Complex.zero_im
  have hc1 := real_case hm hν hbu ht₁ ht₁₂ hBz hF hp₀ hd₀ hre hrec hδ
    (fun z h1 h2 => by simp [hv z h1 h2]) W₁ hW₁
  have hc2 := real_case hm hν hbu ht₁ ht₁₂ hBz hF hp₀ hd₀ him himc hδ
    (fun z h1 h2 => by simp [hv z h1 h2]) W₂ hW₂
  have hfun : (fun p : ℝ × ℝ => F_rel p.1 p.2 W) =
      fun p => F_rel p.1 p.2 W₁ + Complex.I • F_rel p.1 p.2 W₂ := by
    funext p; rw [hsplit, map_add, map_smul]
  rw [hfun]
  exact hc1.add (hc2.const_smul Complex.I)

end UnforcedLeray.Short.IIIa.RelB4locAux

namespace UnforcedLeray.Short.IIIa.RelRegularityOrg2

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsMildSub

/-- **`RelB4loc`** (SP 2941-2970): near every point of the block triangle the pinned relative free
evolution is strongly continuous on the dense class of smooth compactly supported fields vanishing
near the boundary lines of the cell at the start age of the point. -/
theorem relB4loc_leaf (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.RelRegularityOrg2.RelB4loc κ := by
  intro P m K B b ν tr t₁ t₂ ctx F_rel hF p₀ hp₀
  obtain ⟨-, -, hm, -, -, hν, -, hbu, ht₁, ht₁₂, -, hBz⟩ := ctx
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨hσ₀, hστ₀, hτ₀⟩ := id hp₀
  have hs₀ : 0 ≤ ageAt ν t₁ p₀.2 :=
    ht₁.trans (RelB4locAux.ageAt_props hν ht₁ ht₁₂ hBz hσ₀ hστ₀ hτ₀).1
  have ha₀ : 0 < clockA ν (ageAt ν t₁ p₀.2) := by unfold clockA; positivity
  refine ⟨RelB4locAux.denseClass m (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ p₀.2))),
    RelB4locAux.dense_denseClass m (div_pos hc (Real.sqrt_pos.2 ha₀)), fun W hW => ?_⟩
  exact RelB4locAux.complex_case hm hν hbu ht₁ ht₁₂ hBz hF hp₀ rfl hW

end UnforcedLeray.Short.IIIa.RelRegularityOrg2
