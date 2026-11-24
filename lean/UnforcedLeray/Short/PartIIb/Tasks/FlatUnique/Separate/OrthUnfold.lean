import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.PerNice
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.PeriodicUnfold
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.AgeCell

/-!
# Part II-b, leaf `PartII-b:T11/6/11` (`OrthUnfold`): unfolding the orthogonality

Source of record: `the November 2 reference manuscript`, SP 1921-1938 (the
periodization over translates of the cell, used silently).

Proof. Fix a time test `θ` and a smooth compactly supported `ψ`, and let `ζ` be the nice stream
of `PerNice` for `ψ`. Put `A x = streamPair b θ ψ x`.

1. `A` is integrable on `Coord` (box integrability of `b`, bounded coefficients supported in a box).
2. The strips `pucStrip c n` partition `Coord`, so `∫ A = Σ_n ∫_{strip n} A`.
3. `∫_{strip n} A = ∫_{univ × cell} ounTerm (n c)` by `puc_setIntegral_strip` and a.e.
   `c`-periodicity of `b`, where `ounTerm a y = Σ_i b y i · θ(y.1) ∂_i^⊥ψ(y.2.1 + a, y.2.2)`.
4. Only the finite window `|n| ≤ N` contributes (`puc_big_shift`), and on the cell the window sum
   of `ounTerm (n c)` equals `streamPair b θ ζ` (`PerNice`).
5. `θ = 0` for `s ≤ 0`, so the cell integral over `univ × cell` is the integral over
   `Ioi 0 × cell`, which is `c⁻¹` times the integral against `ageμ c 0` (`ageμ_zero_eq`), zero by
   `NiceOrth`.

Helpers use the prefix `oun`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The `a`-shifted pairing integrand `Σ_i b_i · θ(s) ∂_i^⊥ψ(q + a, η)` on the chart. -/
def ounTerm (b : CProf) (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (a : ℝ) (x : Coord) : ℂ :=
  ∑ i : Fin 2, b x i * ((θ x.1 * perpGrad ψ (x.2.1 + a, x.2.2) i : ℝ) : ℂ)

theorem oun_perp_cont (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => perpGrad ψ p i) := by
  have hd : Continuous (fun p : ℝ × ℝ => fderiv ℝ ψ p) := hψ.continuous_fderiv (by simp)
  fin_cases i
  · exact hd.clm_apply continuous_const
  · exact (hd.clm_apply continuous_const).neg

theorem oun_perp_bdd (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∃ C : ℝ, ∀ (p : ℝ × ℝ) (i : Fin 2), ‖perpGrad ψ p i‖ ≤ C := by
  have hd : Continuous (fun p : ℝ × ℝ => fderiv ℝ ψ p) := hψ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support (hψc.fderiv (𝕜 := ℝ))
  have key : ∀ (p : ℝ × ℝ) (v : ℝ × ℝ), ‖v‖ ≤ 1 → ‖fderiv ℝ ψ p v‖ ≤ C := fun p v hv =>
    ((fderiv ℝ ψ p).le_opNorm v).trans ((mul_le_of_le_one_right (norm_nonneg _) hv).trans (hC p))
  refine ⟨C, fun p i => ?_⟩
  fin_cases i
  · exact key p (0, 1) (by simp [Prod.norm_def])
  · simpa [perpGrad, norm_neg] using key p (1, 0) (by simp [Prod.norm_def])

theorem oun_perp_supp (ψ : ℝ × ℝ → ℝ) (hψc : HasCompactSupport ψ) :
    ∃ A : ℝ, ∀ (p : ℝ × ℝ) (i : Fin 2), perpGrad ψ p i ≠ 0 → |p.1| ≤ A ∧ |p.2| ≤ A := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1
    hψc.isCompact.isBounded
  refine ⟨r, fun p i hp => ?_⟩
  have hmem : p ∈ tsupport ψ := by
    by_contra hn
    have h0 : fderiv ℝ ψ p = 0 := by
      by_contra hne
      exact hn (support_fderiv_subset (𝕜 := ℝ) (f := ψ) (Function.mem_support.2 hne))
    apply hp
    fin_cases i <;> simp [perpGrad, h0]
  have hball := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  have h1 := (norm_fst_le p).trans hball
  have h2 := (norm_snd_le p).trans hball
  rw [Real.norm_eq_abs] at h1 h2
  exact ⟨h1, h2⟩

theorem oun_theta_bdd (θ : ℝ → ℝ) (hθ : TimeTest θ) : ∃ M : ℝ, ∀ s : ℝ, ‖θ s‖ ≤ M :=
  hθ.smooth.continuous.bounded_above_of_compact_support hθ.compact

theorem oun_time_bounds (θ : ℝ → ℝ) (hθ : TimeTest θ) :
    ∃ σ Hh : ℝ, 0 < σ ∧ ∀ s : ℝ, θ s ≠ 0 → σ ≤ s ∧ s ≤ Hh := by
  obtain ⟨Hh, hH⟩ := hθ.compact.isCompact.isBounded.exists_norm_le
  by_cases hne : (tsupport θ).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hθ.compact.isCompact.exists_isMinOn hne continuousOn_id
    refine ⟨m, Hh, Set.mem_Ioi.1 (hθ.supp hm), fun s hs => ⟨?_, ?_⟩⟩
    · exact hmin (subset_tsupport θ hs)
    · have h1 := hH s (subset_tsupport θ hs)
      rw [Real.norm_eq_abs] at h1
      exact (le_abs_self s).trans h1
  · exact ⟨1, Hh, one_pos, fun s hs => absurd ⟨s, subset_tsupport θ hs⟩ hne⟩

/-- Box integrability of a single component against a bounded continuous coefficient vanishing
outside the box. -/
theorem oun_box_int (b : CProf) (i : Fin 2) (B : Set Coord) (f : Coord → ℝ) (M : ℝ)
    (hB : IntegrableOn (fun x : Coord => b x i) B volume) (hf : Continuous f)
    (hM : ∀ x, ‖f x‖ ≤ M) (hsupp : ∀ x, x ∉ B → f x = 0) :
    Integrable (fun x : Coord => b x i * ((f x : ℝ) : ℂ)) volume := by
  have h1 : IntegrableOn (fun x : Coord => ((f x : ℝ) : ℂ) * b x i) B volume :=
    Integrable.bdd_mul hB (Complex.continuous_ofReal.comp hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Complex.norm_real]; exact hM x)
  have hs : Function.support (fun x : Coord => ((f x : ℝ) : ℂ) * b x i) ⊆ B := by
    intro x hx
    by_contra hxB
    exact hx (by simp [hsupp x hxB])
  have h2 : Integrable (fun x : Coord => ((f x : ℝ) : ℂ) * b x i) volume :=
    (integrableOn_iff_integrable_of_support_subset hs).1 h1
  exact h2.congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem oun_integrable (b : CProf) (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (hθ : TimeTest θ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (σ Hh A : ℝ)
    (hθs : ∀ s : ℝ, θ s ≠ 0 → σ ≤ s ∧ s ≤ Hh)
    (hA : ∀ (p : ℝ × ℝ) (i : Fin 2), perpGrad ψ p i ≠ 0 → |p.1| ≤ A ∧ |p.2| ≤ A)
    (hbox : ∀ (R : ℝ) (i : Fin 2), IntegrableOn (fun x : Coord => b x i)
      (Icc σ Hh ×ˢ (Icc (-R) R ×ˢ Icc (-A) A)) volume) (a : ℝ) :
    Integrable (ounTerm b θ ψ a) volume := by
  obtain ⟨Mθ, hMθ⟩ := oun_theta_bdd θ hθ
  obtain ⟨Cψ, hCψ⟩ := oun_perp_bdd ψ hψ hψc
  have hterm : ∀ i : Fin 2, Integrable
      (fun x : Coord => b x i * ((θ x.1 * perpGrad ψ (x.2.1 + a, x.2.2) i : ℝ) : ℂ)) volume := by
    intro i
    refine oun_box_int b i (Icc σ Hh ×ˢ (Icc (-(A + |a|)) (A + |a|) ×ˢ Icc (-A) A))
      (fun x : Coord => θ x.1 * perpGrad ψ (x.2.1 + a, x.2.2) i) (Mθ * Cψ)
      (hbox _ i) ?_ ?_ ?_
    · exact (hθ.smooth.continuous.comp continuous_fst).mul
        ((oun_perp_cont ψ hψ i).comp (by fun_prop))
    · intro x
      rw [norm_mul]
      exact mul_le_mul (hMθ _) (hCψ _ _) (norm_nonneg _) ((norm_nonneg _).trans (hMθ 0))
    · intro x hx
      by_contra hne
      have hp : θ x.1 ≠ 0 := fun h0 => hne (by simp [h0])
      have hq : perpGrad ψ (x.2.1 + a, x.2.2) i ≠ 0 := fun h0 => hne (by simp [h0])
      obtain ⟨h1, h2⟩ := hθs x.1 hp
      obtain ⟨h3, h4⟩ := hA (x.2.1 + a, x.2.2) i hq
      dsimp only at h3 h4
      obtain ⟨h5, h6⟩ := abs_le.1 h3
      obtain ⟨h7, h8⟩ := abs_le.1 h4
      exact hx ⟨⟨h1, h2⟩, ⟨⟨by linarith [neg_abs_le a, le_abs_self a],
        by linarith [neg_abs_le a, le_abs_self a]⟩, ⟨h7, h8⟩⟩⟩
  show Integrable (fun x : Coord =>
    ∑ i : Fin 2, b x i * ((θ x.1 * perpGrad ψ (x.2.1 + a, x.2.2) i : ℝ) : ℂ)) volume
  exact integrable_finsetSum _ fun i _ => hterm i

/-- The strip integral of the pairing is the cell integral of the `n c`-shifted term. -/
theorem oun_strip (b : CProf) (θ : ℝ → ℝ) (ψ : ℝ × ℝ → ℝ) (c : ℝ) (hper : QPeriodic c b)
    (hθ0 : ∀ s : ℝ, s ≤ 0 → θ s = 0) (n : ℤ) :
    ∫ x in pucStrip c n, streamPair b θ ψ x =
      ∫ y in univ ×ˢ Cyl.cell c, ounTerm b θ ψ ((n : ℝ) * c) y := by
  rw [puc_setIntegral_strip (fun x : Coord => streamPair b θ ψ x) c n]
  refine setIntegral_congr_ae (MeasurableSet.prod MeasurableSet.univ (Cyl.measurableSet_cell c))
    ?_
  -- `b` is periodic on `s > 0` only (`QPeriodic`); its cut-off `1_{s>0} b` is periodic everywhere
  have hG : ∀ i : Fin 2, ∀ᵐ x : Coord,
      ({x : Coord | 0 < x.1}.indicator fun x => b x i) (qShift c x) =
        ({x : Coord | 0 < x.1}.indicator fun x => b x i) x := fun i =>
    QPerHalf.indicator_ae le_rfl ((QPerHalf.ae_imp hper).mono fun x hx hx0 => by
      simp only [hx hx0])
  have hall : ∀ᵐ y : Coord, ∀ i : Fin 2,
      ({x : Coord | 0 < x.1}.indicator fun x => b x i) (qShift ((n : ℝ) * c) y) =
        ({x : Coord | 0 < x.1}.indicator fun x => b x i) y :=
    ae_all_iff.2 fun i => puc_ae_shift_int (hG i) n
  filter_upwards [hall] with y hy
  intro _
  show ∑ i : Fin 2, b (qShift ((n : ℝ) * c) y) i *
      ((θ y.1 * perpGrad ψ (y.2.1 + (n : ℝ) * c, y.2.2) i : ℝ) : ℂ) =
    ∑ i : Fin 2, b y i * ((θ y.1 * perpGrad ψ (y.2.1 + (n : ℝ) * c, y.2.2) i : ℝ) : ℂ)
  by_cases hy0 : 0 < y.1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h : b (qShift ((n : ℝ) * c) y) i = b y i := by
      have h' := hy i
      rwa [Set.indicator_of_mem (show qShift ((n : ℝ) * c) y ∈ {x : Coord | 0 < x.1} from hy0),
        Set.indicator_of_mem (show y ∈ {x : Coord | 0 < x.1} from hy0)] at h'
    rw [h]
  · -- off the half space the time cut-off vanishes
    simp only [hθ0 y.1 (not_lt.1 hy0), zero_mul, Complex.ofReal_zero, mul_zero]

/-- **Leaf `PartII-b:T11/6/11`** (unfolding the orthogonality; uses `T11/6/10`). -/
theorem orthUnfold : UnforcedLeray.Short.IIb.OrthUnfold := by
  intro c r b hc hr hb hNice θ ψ hθ hψ hψc
  obtain ⟨σ, Hh, hσ, hθs⟩ := oun_time_bounds θ hθ
  have hθ0 : ∀ s : ℝ, s ≤ 0 → θ s = 0 := fun s hs => by
    by_contra hne
    exact absurd (lt_of_lt_of_le hσ (hθs s hne).1) (not_lt.2 hs)
  obtain ⟨A, hA⟩ := oun_perp_supp ψ hψc
  have hbox : ∀ (R : ℝ) (i : Fin 2), IntegrableOn (fun x : Coord => b x i)
      (Icc σ Hh ×ˢ (Icc (-R) R ×ˢ Icc (-A) A)) volume :=
    fun R i => hrBoxIntegrable c r b hc hr hb σ Hh R A hσ i
  have hint := oun_integrable b θ ψ hθ hψ hψc σ Hh A hθs hA hbox
  obtain ⟨ζ, hζ, hperp⟩ := perNice c ψ hc hψ hψc
  have hIntA : Integrable (fun x : Coord => streamPair b θ ψ x) volume :=
    (hint 0).congr (Filter.Eventually.of_forall fun x => by simp [streamPair, ounTerm])
  -- strip decomposition
  have hsplit : ∫ x : Coord, streamPair b θ ψ x =
      ∑' n : ℤ, ∫ x in pucStrip c n, streamPair b θ ψ x := by
    have hU : IntegrableOn (fun x : Coord => streamPair b θ ψ x) (⋃ n : ℤ, pucStrip c n) volume := by
      rw [puc_iUnion_strip hc]
      exact hIntA.integrableOn
    have h1 := integral_iUnion (fun n => puc_measurableSet_strip c n)
      (puc_pairwise_disjoint hc) hU
    rw [puc_iUnion_strip hc, setIntegral_univ] at h1
    exact h1
  -- the window of strips that can meet the cell
  obtain ⟨N, hN⟩ := exists_int_gt ((A + c) / c)
  have hzero : ∀ n : ℤ, n ∉ Finset.Icc (-N) N →
      ∫ x in pucStrip c n, streamPair b θ ψ x = 0 := by
    intro n hn
    rw [oun_strip b θ ψ c hb.periodic hθ0 n]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    have hq := Cyl.mem_cell.1 hy.2
    have hbig := puc_big_shift hc hN hq.1 hq.2 hn
    unfold ounTerm
    refine Finset.sum_eq_zero fun i _ => ?_
    have h0 : perpGrad ψ (y.2.1 + (n : ℝ) * c, y.2.2) i = 0 := by
      by_contra hne
      have := (hA _ i hne).1
      dsimp only at this
      linarith
    rw [h0]
    simp
  have hsplit2 : ∫ x : Coord, streamPair b θ ψ x =
      ∑ n ∈ Finset.Icc (-N) N, ∫ y in univ ×ˢ Cyl.cell c, ounTerm b θ ψ ((n : ℝ) * c) y := by
    rw [hsplit, tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      (f := fun n : ℤ => ∫ x in pucStrip c n, streamPair b θ ψ x)
      (s := Finset.Icc (-N) N) hzero]
    exact Finset.sum_congr rfl fun n _ => oun_strip b θ ψ c hb.periodic hθ0 n
  have hcellsum : ∑ n ∈ Finset.Icc (-N) N, ∫ y in univ ×ˢ Cyl.cell c, ounTerm b θ ψ ((n : ℝ) * c) y
      = ∫ y in univ ×ˢ Cyl.cell c, ∑ n ∈ Finset.Icc (-N) N, ounTerm b θ ψ ((n : ℝ) * c) y := by
    exact (integral_finsetSum (μ := volume.restrict (univ ×ˢ Cyl.cell c))
      (f := fun n : ℤ => ounTerm b θ ψ ((n : ℝ) * c)) (Finset.Icc (-N) N)
      fun n _ => (hint ((n : ℝ) * c)).integrableOn).symm
  -- on the cell the window sum is the stream pairing with `ζ`
  have hpt : ∀ y ∈ univ ×ˢ Cyl.cell c,
      ∑ n ∈ Finset.Icc (-N) N, ounTerm b θ ψ ((n : ℝ) * c) y = streamPair b θ ζ y := by
    rintro y ⟨-, hy⟩
    have hq := Cyl.mem_cell.1 hy
    have hz : ∀ i : Fin 2, perpGrad ζ y.2 i =
        ∑ n ∈ Finset.Icc (-N) N, perpGrad ψ (y.2.1 + (n : ℝ) * c, y.2.2) i := by
      intro i
      rw [hperp y.2 i]
      apply tsum_eq_sum (L := SummationFilter.unconditional ℤ)
      intro n hn
      have hbig := puc_big_shift hc hN hq.1 hq.2 hn
      by_contra hne
      have := (hA _ i hne).1
      dsimp only at this
      linarith
    unfold streamPair ounTerm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hz i, Finset.mul_sum, Complex.ofReal_sum]
  have hcell_eq : ∫ y in univ ×ˢ Cyl.cell c,
      ∑ n ∈ Finset.Icc (-N) N, ounTerm b θ ψ ((n : ℝ) * c) y
      = ∫ y in univ ×ˢ Cyl.cell c, streamPair b θ ζ y :=
    setIntegral_congr_fun (MeasurableSet.prod MeasurableSet.univ (Cyl.measurableSet_cell c)) hpt
  -- the cell integral over `univ` is the one over `Ioi 0`
  have hIoi : ∫ y in univ ×ˢ Cyl.cell c, streamPair b θ ζ y =
      ∫ y in Ioi (0 : ℝ) ×ˢ Cyl.cell c, streamPair b θ ζ y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (MeasurableSet.prod MeasurableSet.univ (Cyl.measurableSet_cell c))
    · exact prod_mono (subset_univ _) subset_rfl
    · intro x hx
      have hx1 : x.1 ≤ 0 := by
        by_contra h
        exact hx.2 ⟨not_le.1 h, hx.1.2⟩
      have hθ0 : θ x.1 = 0 := by
        by_contra hne
        have := (hθs x.1 hne).1
        linarith
      simp [streamPair, hθ0]
  -- the orthogonality hypothesis on the cell `(0, ∞) × cell`
  have hNiceI := hNice θ ζ hθ hζ
  rw [UnforcedLeray.Short.IIb.CellPart.ageμ_zero_eq c, integral_smul_measure] at hNiceI
  have hk : (ENNReal.ofReal c⁻¹).toReal = c⁻¹ := ENNReal.toReal_ofReal (inv_nonneg.2 hc.le)
  rw [hk, smul_eq_zero] at hNiceI
  have hXI : ∫ y in Ioi (0 : ℝ) ×ˢ Cyl.cell c, streamPair b θ ζ y = 0 :=
    hNiceI.resolve_left (inv_ne_zero hc.ne')
  rw [hsplit2, hcellsum, hcell_eq, hIoi, hXI]

end UnforcedLeray.Short.IIb
