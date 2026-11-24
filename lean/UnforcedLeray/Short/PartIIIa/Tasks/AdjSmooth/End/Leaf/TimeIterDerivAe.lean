import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Sub.PartIIIa_T21_2_7_2_1_2_1_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem ha_iter_contDiffOn (φ' : ℝ → ℝ × ℝ → ℂ) (t s : ℝ)
    (hsm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ)) :
    ∀ n : ℕ, ContDiffOn ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => iteratedDeriv n (fun r' => φ' r' p.2) p.1) (Ioo t s ×ˢ univ) := by
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  intro n
  induction n with
  | zero => simpa [iteratedDeriv_zero] using hsm
  | succ n ih =>
    have hfd := ih.fderiv_of_isOpen hU (m := ∞) (by simp)
    refine ContDiffOn.congr (f := fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun q : ℝ × (ℝ × ℝ) => iteratedDeriv n (fun r' => φ' r' q.2) q.1) p
        ((1 : ℝ), (0 : ℝ × ℝ))) ?_ ?_
    · exact hfd.clm_apply contDiffOn_const
    · rintro ⟨r0, y⟩ hp
      have hp' : (r0, y) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) := hp
      have hdiff : DifferentiableAt ℝ
          (fun q : ℝ × (ℝ × ℝ) => iteratedDeriv n (fun r' => φ' r' q.2) q.1) (r0, y) :=
        (ih.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp')
      have hline : HasDerivAt (fun r' : ℝ => ((r', y) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) r0 :=
        (hasDerivAt_id r0).prodMk (hasDerivAt_const r0 y)
      have hd := hdiff.hasFDerivAt.comp_hasDerivAt r0 hline
      show iteratedDeriv (n + 1) (fun r' => φ' r' y) r0 = _
      rw [iteratedDeriv_succ]
      exact hd.deriv

theorem ha_slice_contDiff (φ' : ℝ → ℝ × ℝ → ℂ) (t s : ℝ)
    (hsm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ))
    (n : ℕ) (r : ℝ) (hr : r ∈ Ioo t s) :
    ContDiff ℝ ∞ (fun y => iteratedDeriv n (fun r' => φ' r' y) r) := by
  have hy : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => ((r, y) : ℝ × (ℝ × ℝ))) univ :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have h1 := (ha_iter_contDiffOn φ' t s hsm n).comp hy
    (fun y _ => (⟨hr, mem_univ y⟩ : (r, y) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ))))
  exact contDiffOn_univ.mp h1

theorem ha_slice_hasDerivAt (φ' : ℝ → ℝ × ℝ → ℂ) (t s : ℝ)
    (hsm : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ioo t s ×ˢ univ))
    (n : ℕ) (x : ℝ × ℝ) (r : ℝ) (hr : r ∈ Ioo t s) :
    HasDerivAt (fun r' => iteratedDeriv n (fun r'' => φ' r'' x) r')
      (iteratedDeriv (n + 1) (fun r'' => φ' r'' x) r) r := by
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hdiff : DifferentiableAt ℝ
      (fun q : ℝ × (ℝ × ℝ) => iteratedDeriv n (fun r' => φ' r' q.2) q.1) (r, x) :=
    ((ha_iter_contDiffOn φ' t s hsm n).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (⟨hr, mem_univ x⟩ : (r, x) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ))))
  have hline : HasDerivAt (fun r' : ℝ => ((r', x) : ℝ × (ℝ × ℝ))) ((1 : ℝ), (0 : ℝ × ℝ)) r :=
    (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt r hline
  have hD : DifferentiableAt ℝ (iteratedDeriv n (fun r' => φ' r' x)) r := hd.differentiableAt
  rw [iteratedDeriv_succ]
  exact hD.hasDerivAt

theorem ha_seq (t s r : ℝ) (hr : r ∈ Ioo t s) :
    ∃ rn : ℕ → ℝ, (∀ n, rn n ∈ Ioo t s ∧ rn n ≠ r) ∧ Tendsto rn atTop (𝓝 r) := by
  obtain ⟨hr1, hr2⟩ := hr
  refine ⟨fun n => r + (s - r) / 2 * (1 / ((n : ℝ) + 1)), fun n => ?_, ?_⟩
  · have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h2 : 0 < (s - r) / 2 * (1 / ((n : ℝ) + 1)) := mul_pos (by linarith) h0
    have h3 : (s - r) / 2 * (1 / ((n : ℝ) + 1)) ≤ (s - r) / 2 := by
      have : (0 : ℝ) ≤ (s - r) / 2 := by linarith
      nlinarith
    exact ⟨⟨by linarith, by linarith⟩, ne_of_gt (by linarith)⟩
  · have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((s - r) / 2)).const_add r
    simpa using this

theorem timeIterDerivAe : UnforcedLeray.Short.IIIa.TimeIterDerivAe := by
  intro c m t s Φ φ' hc hts hΦ hae hsm
  have hper : ∀ n : ℕ, ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, Φ n r (x.1 + c, x.2) = Φ n r x := by
    intro n r hr x
    obtain ⟨D, hD, -⟩ := hΦ.1 n 0
    rw [← (hD r hr).base]
    exact (hD r hr).periodic [] (by simp) x
  have hF : ∀ n : ℕ, ∀ r ∈ Ico t s, AEStronglyMeasurable (Φ n r) (B0579.cellMeasure c (-m)) := by
    intro n r hr
    obtain ⟨D, hD, -⟩ := hΦ.1 n 0
    have h := (hD r hr).memX [] (by simp)
    rw [(hD r hr).base] at h
    exact h.aestronglyMeasurable
  have hac : B0579.cellMeasure c (-m) ≪ volume :=
    (B0579.cellMeasure_ac c (-m)).trans Measure.restrict_le_self.absolutelyContinuous
  have hback : volume.restrict (B0579.cell c) ≪ B0579.cellMeasure c (-m) :=
    B0579.ac_cellMeasure c (-m)
  intro j
  induction j with
  | zero =>
    intro r hr
    filter_upwards [hae r hr] with x hx
    show iteratedDeriv 0 (fun r' => φ' r' x) r = Φ 0 r x
    rw [iteratedDeriv_zero]
    exact hx
  | succ j ih =>
    intro r hr
    have hrI : r ∈ Ico t s := ⟨hr.1.le, hr.2⟩
    obtain ⟨rn, hrn, hlim⟩ := ha_seq t s r hr
    have hrnI : ∀ n, rn n ∈ Ico t s := fun n => ⟨(hrn n).1.1.le, (hrn n).1.2⟩
    have ihx : ∀ r' ∈ Ioo t s, ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)),
        iteratedDeriv j (fun r'' => φ' r'' x) r' = Φ j r' x := fun r' hr' => ih r' hr'
    have hcont : ∀ n, Continuous (fun x : ℝ × ℝ =>
        (((rn n - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' x) (rn n) - iteratedDeriv j (fun r' => φ' r' x) r)) := by
      intro n
      exact continuous_const.mul
        ((ha_slice_contDiff φ' t s hsm j (rn n) (hrn n).1).continuous.sub
          (ha_slice_contDiff φ' t s hsm j r hr).continuous)
    have hEq : ∀ n, (fun x : ℝ × ℝ =>
        (((rn n - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' x) (rn n) - iteratedDeriv j (fun r' => φ' r' x) r))
          =ᵐ[volume] (fun x : ℝ × ℝ =>
        (((rn n - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn n) x - Φ j r x)) := by
      intro n
      filter_upwards [ihx (rn n) (hrn n).1, ihx r hr] with x h1 h2
      simp only [h1, h2]
    have hconv : Tendsto (fun n => eLpNorm ((fun x : ℝ × ℝ =>
        (((rn n - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn n) x - Φ j r x)) - Φ (j + 1) r) 2
        (B0579.cellMeasure c (-m))) atTop (𝓝 0) := by
      have h := (hΦ.2 j r hrI).comp (tendsto_nhdsWithin_iff.2
        ⟨hlim, Eventually.of_forall fun n => ⟨hrnI n, (hrn n).2⟩⟩)
      exact h
    have hmeasQ : ∀ n, AEStronglyMeasurable (fun x : ℝ × ℝ =>
        (((rn n - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn n) x - Φ j r x)) (B0579.cellMeasure c (-m)) :=
      fun n => (hcont n).aestronglyMeasurable.congr (hac.ae_le (hEq n))
    have hgF : AEStronglyMeasurable (Φ (j + 1) r) (B0579.cellMeasure c (-m)) :=
      hF (j + 1) r hrI
    have hTIM := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      hmeasQ hgF hconv
    obtain ⟨ns, hns, hae_lim⟩ := hTIM.exists_seq_tendsto_ae
    have hslope : ∀ x : ℝ × ℝ, Tendsto (fun n =>
        (((rn n - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' x) (rn n) - iteratedDeriv j (fun r' => φ' r' x) r))
        atTop (𝓝 (iteratedDeriv (j + 1) (fun r' => φ' r' x) r)) := by
      intro x
      have hd := (hasDerivAt_iff_tendsto_slope).1 (ha_slice_hasDerivAt φ' t s hsm j x r hr)
      have hn : Tendsto rn atTop (𝓝[≠] r) :=
        tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hrn n).2⟩
      have h := hd.comp hn
      refine Tendsto.congr (fun n => ?_) h
      simp only [Function.comp_apply, slope_def_module, Complex.real_smul]
    have hQper : ∀ n, ∀ x : ℝ × ℝ,
        (((rn n - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn n) (x.1 + c, x.2) - Φ j r (x.1 + c, x.2))
          = (((rn n - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn n) x - Φ j r x) := by
      intro n x
      rw [hper j _ (hrnI n) x, hper j r hrI x]
    have hCper : ∀ n, ∀ x : ℝ × ℝ,
        (((rn n - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' (x.1 + c, x.2)) (rn n) -
            iteratedDeriv j (fun r' => φ' r' (x.1 + c, x.2)) r)
          = (((rn n - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' x) (rn n) - iteratedDeriv j (fun r' => φ' r' x) r) := by
      intro n x
      have hp := adjPeriodic_of_ae_eq (hcont n) (hEq n)
        (fun y => by
          show (((rn n - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn n) (y.1 + c, y.2) - Φ j r (y.1 + c, y.2))
            = (((rn n - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn n) y - Φ j r y)
          exact hQper n y) x
      exact hp
    have hΨper : ∀ x : ℝ × ℝ,
        iteratedDeriv (j + 1) (fun r' => φ' r' (x.1 + c, x.2)) r =
          iteratedDeriv (j + 1) (fun r' => φ' r' x) r := by
      intro x
      have h2 : Tendsto (fun n => (((rn n - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' (x.1 + c, x.2)) (rn n) -
            iteratedDeriv j (fun r' => φ' r' (x.1 + c, x.2)) r))
          atTop (𝓝 (iteratedDeriv (j + 1) (fun r' => φ' r' x) r)) := by
        refine Tendsto.congr (fun n => ?_) (hslope x)
        exact (hCper n x).symm
      exact tendsto_nhds_unique (hslope (x.1 + c, x.2)) h2
    have hall : ∀ᵐ x ∂(B0579.cellMeasure c (-m)), ∀ i,
        (((rn (ns i) - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' x) (rn (ns i)) - iteratedDeriv j (fun r' => φ' r' x) r)
          = (((rn (ns i) - r)⁻¹ : ℝ) : ℂ) * (Φ j (rn (ns i)) x - Φ j r x) :=
      ae_all_iff.2 fun i => hac.ae_le (hEq (ns i))
    have hμae : ∀ᵐ x ∂(B0579.cellMeasure c (-m)),
        iteratedDeriv (j + 1) (fun r' => φ' r' x) r = Φ (j + 1) r x := by
      filter_upwards [hae_lim, hall] with x hx hxi
      have h1 : Tendsto (fun i => (((rn (ns i) - r)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv j (fun r' => φ' r' x) (rn (ns i)) - iteratedDeriv j (fun r' => φ' r' x) r))
          atTop (𝓝 (Φ (j + 1) r x)) := hx.congr (fun i => (hxi i).symm)
      exact tendsto_nhds_unique ((hslope x).comp hns.tendsto_atTop) h1
    have hpl : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
        iteratedDeriv (j + 1) (fun r' => φ' r' x) r = Φ (j + 1) r x :=
      hback.ae_le hμae
    have hfinal := periodicAeOfCell c hc
      (fun x => iteratedDeriv (j + 1) (fun r' => φ' r' x) r) (Φ (j + 1) r)
      (fun x => hΨper x) (fun x => hper (j + 1) r hrI x) hpl
    exact hfinal

end UnforcedLeray.Short.IIIa
