import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.PeriodicUnfold

/-!
# Part II-b, leaf `PartII-b:T11/6/14` (`HrStripLp`): `H_r` norm integrability on strips

Source of record: `the November 2 reference manuscript`, SP 1900-1903 (the space
`H_r`, `s^{r/2-5/2} ds dq/c dη`). Statement: `HrStripLp` of `Sub/T11_6.lean`.

Proof, self-contained up to the audited lemmas of `Tasks/FlatUnique/CellStream/HrBox.lean`:
1. `b' := (InHr.meas).mk b` is strongly measurable and `b = b'` `hMeas`-a.e.
2. Lebesgue measure on `(0,∞) × cell` is absolutely continuous with respect to `ageμ`
   (`hrBox_ac`), and `b` is `QPeriodic`, so `b x = b' (hrBoxRed c x)` for a.e. `x` with `s > 0`.
3. The strip `[σ,H] × [-R,R] × ℝ` is covered by finitely many `q`-translates of the cell
   `[-c/2, c/2) × ℝ` (`Cyl.cell c` already contains all of `η`), so its `‖b'∘hrBoxRed‖ₑ^r`
   integral is at most a finite sum of translates of `hrBoxG`, each of finite Lebesgue integral
   (`hrBox_lintegral_G_bound`, measure preservation `hrBox_qShift_mp`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T11/6/14`** (`H_r` is `L^r` on strip boxes): for `b ∈ H_r`, `r > 1`, `0 < σ`
and any `H, R`, `∫⁻_{[σ,H] × [-R,R] × ℝ} ‖b‖ₑ^r < ∞`. -/
theorem hrStripLp : UnforcedLeray.Short.IIb.HrStripLp := by
  intro c r b hc hr hb σ H R hσ
  have hr0 : 0 < r := by linarith
  obtain ⟨b', hb'sm, hbb'⟩ : ∃ b' : CProf, StronglyMeasurable b' ∧
      ∀ᵐ y ∂(hMeas c r), b y = b' y :=
    ⟨hb.meas.mk b, hb.meas.stronglyMeasurable_mk, hb.meas.ae_eq_mk⟩
  have hb'm : Measurable b' := hb'sm.measurable
  have hfin : ∫⁻ y, ‖b y‖ₑ ^ r ∂(hMeas c r) < ⊤ := by
    have h0 : eLpNorm b (ENNReal.ofReal r) (hMeas c r) < ⊤ := hb.finite
    have h1 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top).1 h0
    rwa [ENNReal.toReal_ofReal hr0.le] at h1
  have hX : ∫⁻ y, hrBoxG c r σ H b' y ∂volume < ⊤ :=
    hrBox_lintegral_G_bound (H := H) hc hσ hb'm hbb' hfin
  -- periodicity for all integer shifts, and the Lebesgue a.e. identity on the cell
  have hper : QPeriodic c b := hb.periodic
  have hper' : ∀ n : ℤ, ∀ᵐ x : Coord, 0 < x.1 → b (qShift ((n : ℝ) * c) x) = b x :=
    fun n => hrBox_shiftPer_all hper n
  have hAll : ∀ᵐ x : Coord, ∀ n : ℤ, 0 < x.1 → b (qShift ((n : ℝ) * c) x) = b x :=
    ae_all_iff.2 hper'
  have hS0ae : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Cyl.cell c)), b y = b' y :=
    (hrBox_ac hc (r / 2 - 5 / 2)).ae_le hbb'
  have hS0 : ∀ᵐ y : Coord, y ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c → b y = b' y :=
    (ae_restrict_iff' (MeasurableSet.prod measurableSet_Ioi (hrBox_cell_measurable c))).1 hS0ae
  have hE : ∀ n : ℤ, ∀ᵐ x : Coord, qShift ((n : ℝ) * c) x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c →
      b (qShift ((n : ℝ) * c) x) = b' (qShift ((n : ℝ) * c) x) :=
    fun n => ((hrBox_qShift_mp ((n : ℝ) * c)).quasiMeasurePreserving).ae hS0
  have hEall : ∀ᵐ x : Coord, ∀ n : ℤ, qShift ((n : ℝ) * c) x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c →
      b (qShift ((n : ℝ) * c) x) = b' (qShift ((n : ℝ) * c) x) :=
    ae_all_iff.2 hE
  -- the pointwise identity `b x = b' (hrBoxRed c x)` for a.e. `x` with `s > 0`
  have hpt : ∀ᵐ x : Coord, 0 < x.1 → b x = b' (hrBoxRed c x) := by
    filter_upwards [hAll, hEall] with x hA hE' hx
    have hmem : qShift (((-(hrBoxK c x) : ℤ) : ℝ) * c) x ∈ Ioi (0 : ℝ) ×ˢ Cyl.cell c :=
      hrBox_red_mem hc (Ioi 0) x hx
    exact (hA (-(hrBoxK c x)) hx).symm.trans (hE' (-(hrBoxK c x)) hmem)
  -- the finite index set of translates
  obtain ⟨N, hN⟩ : ∃ N : ℤ, |R| + c ≤ (N : ℝ) * c :=
    ⟨⌈(|R| + c) / c⌉, (div_le_iff₀ hc).1 (Int.le_ceil _)⟩
  have hkF : ∀ x ∈ Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ)),
      -(hrBoxK c x) ∈ Finset.Icc (-N) N := by
    intro x hx
    have hq : x.2.1 ∈ Icc (-R) R := (Set.mem_prod.1 (Set.mem_prod.1 hx).2).1
    have hq1 : -|R| ≤ x.2.1 := le_trans (neg_le_neg (le_abs_self R)) hq.1
    have hq2 : x.2.1 ≤ |R| := le_trans hq.2 (le_abs_self R)
    obtain ⟨k1, k2⟩ := hrBox_floor_bounds hc x
    have hkN : (hrBoxK c x : ℝ) < N := by
      have h : (hrBoxK c x : ℝ) * c < (N : ℝ) * c := by linarith
      exact lt_of_mul_lt_mul_right h hc.le
    have hNk : -(N : ℝ) < (hrBoxK c x : ℝ) := by
      have h : -(N : ℝ) * c < (hrBoxK c x : ℝ) * c := by
        have e : -(N : ℝ) * c = -((N : ℝ) * c) := by ring
        rw [e]
        linarith
      exact lt_of_mul_lt_mul_right h hc.le
    have hkN' : hrBoxK c x < N := by exact_mod_cast hkN
    have hNk' : -N < hrBoxK c x := by exact_mod_cast hNk
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hBm : MeasurableSet (Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ))) :=
    MeasurableSet.prod measurableSet_Icc
      (MeasurableSet.prod measurableSet_Icc MeasurableSet.univ)
  -- the strip mass is bounded by a finite sum of translates of `hrBoxG`
  have hsum : ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ)), ‖b' (hrBoxRed c x)‖ₑ ^ r
      ∂volume ≤
      ∑ m ∈ Finset.Icc (-N) N, ∫⁻ x, hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x) ∂volume := by
    rw [← lintegral_finsetSum (f := fun (m : ℤ) (x : Coord) =>
      hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x))
      _ (fun m _ => (hrBoxG_measurable hb'm).comp (hrBox_qShift_mp ((m : ℝ) * c)).measurable)]
    rw [← lintegral_indicator hBm]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ))
    · rw [Set.indicator_of_mem hx]
      have hredS : hrBoxRed c x ∈ Icc σ H ×ˢ Cyl.cell c :=
        hrBox_red_mem hc (Icc σ H) x (Set.mem_prod.1 hx).1
      have hG1 : hrBoxG c r σ H b' (hrBoxRed c x) = ‖b' (hrBoxRed c x)‖ₑ ^ r := by
        unfold hrBoxG
        exact Set.indicator_of_mem hredS _
      calc ‖b' (hrBoxRed c x)‖ₑ ^ r = hrBoxG c r σ H b' (hrBoxRed c x) := hG1.symm
        _ ≤ ∑ m ∈ Finset.Icc (-N) N, hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x) :=
          Finset.single_le_sum (f := fun m : ℤ => hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x))
            (fun _ _ => zero_le) (hkF x hx)
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hterm : ∀ m : ℤ, ∫⁻ x, hrBoxG c r σ H b' (qShift ((m : ℝ) * c) x) ∂volume < ⊤ := by
    intro m
    rw [(hrBox_qShift_mp ((m : ℝ) * c)).lintegral_comp (hrBoxG_measurable hb'm)]
    exact hX
  have hXB : ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ)), ‖b' (hrBoxRed c x)‖ₑ ^ r
      ∂volume < ⊤ :=
    lt_of_le_of_lt hsum (ENNReal.sum_lt_top.2 (fun m _ => hterm m))
  -- replace `b` by `b' ∘ hrBoxRed` on the strip (there `s > 0`)
  have hEq : ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ)), ‖b x‖ₑ ^ r ∂volume =
      ∫⁻ x in Icc σ H ×ˢ (Icc (-R) R ×ˢ (univ : Set ℝ)), ‖b' (hrBoxRed c x)‖ₑ ^ r ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hpt, ae_restrict_mem hBm] with x hx hxB
    have hxs : 0 < x.1 := lt_of_lt_of_le hσ (Set.mem_prod.1 hxB).1.1
    show ‖b x‖ₑ ^ r = ‖b' (hrBoxRed c x)‖ₑ ^ r
    rw [hx hxs]
  rw [hEq]
  exact hXB.ne

end UnforcedLeray.Short.IIb
