import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_5
import UnforcedLeray.Short.PartIIb.Sub.T07
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# Part II-b, task `PartII-b:G4/3/5/3` (`ProfileStripExtend`): from the strip to all of `H_p`

Source of record: `the November 2 reference manuscript`, SP 1902-1906.
Model: `DivPeriodicExtend` (`Tasks/GradLapNvC/DivVanish/PeriodicExtend.lean`).

Proof. Put `g_j = b_j - b'_j`.
1. `g_j` is a.e. `c`-periodic in `q` (`InHr.periodic`), hence a.e. invariant under all integer
   `q`-shifts.
2. On the strip `{s > 0, |q| < c/2}` the factor `√s` is nonzero, so `g_j = 0` a.e. there.
3. Translating the strip by integer multiples of `c` and taking the countable intersection,
   `g_j = 0` a.e. on `{s > 0}` (the complement of the strips is the null set `{q = (k-1/2) c}`).
4. Hence `b = b'` a.e. on `{s > 0}` (volume). A volume-null set has `ageμ`-null measurable hull, and
   `ageμ` lives on `{s > 0}` (`ae_ageμ_mem`), giving `b = b'` `hMeas c bgp`-a.e.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace ProfileStripHelp

/-- A function a.e. `c`-periodic on `s > 0` is a.e. invariant there under all integer shifts
`m c` (the shift fixes `s`). -/
theorem per_int {c : ℝ} {g : Coord → ℂ} (hg : ∀ᵐ x : Coord, 0 < x.1 → g (qShift c x) = g x)
    (m : ℤ) : ∀ᵐ x : Coord, 0 < x.1 → g (qShift ((m : ℝ) * c) x) = g x := by
  induction m using Int.induction_on with
  | zero => exact ae_of_all _ (fun x _ => by simp [qShift])
  | succ i ih =>
    have hpull : ∀ᵐ x : Coord, 0 < (qShift (((i : ℤ) : ℝ) * c) x).1 →
        g (qShift c (qShift (((i : ℤ) : ℝ) * c) x)) = g (qShift (((i : ℤ) : ℝ) * c) x) :=
      (hrBox_qShift_mp (((i : ℤ) : ℝ) * c)).quasiMeasurePreserving.ae hg
    filter_upwards [hpull, ih] with x h1 h2 hx0
    have e : c + ((i : ℤ) : ℝ) * c = (((i + 1 : ℤ)) : ℝ) * c := by
      push_cast
      ring
    have h3 := h1 hx0
    rw [hrBox_qShift_qShift, e] at h3
    exact h3.trans (h2 hx0)
  | pred i ih =>
    have hpull : ∀ᵐ x : Coord, 0 < (qShift ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c) x).1 →
        g (qShift c (qShift ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c) x)) =
          g (qShift ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c) x) :=
      (hrBox_qShift_mp ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c)).quasiMeasurePreserving.ae hg
    filter_upwards [hpull, ih] with x h1 h2 hx0
    have e : c + ((((-(i : ℤ) - 1 : ℤ)) : ℝ) * c) = (((-(i : ℤ) : ℤ)) : ℝ) * c := by
      push_cast
      ring
    have h3 := h1 hx0
    rw [hrBox_qShift_qShift, e] at h3
    exact h3.symm.trans (h2 hx0)

/-- From a.e. vanishing on the strip `|q| < c/2, s > 0` to a.e. vanishing on all of `s > 0`,
for a function a.e. `c`-periodic on `s > 0`. -/
theorem strip_all {c : ℝ} (hc : 0 < c) {g : Coord → ℂ}
    (hper : ∀ᵐ x : Coord, 0 < x.1 → g (qShift c x) = g x)
    (A0 : ∀ᵐ x : Coord, x ∈ (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) →
      g x = 0) :
    ∀ᵐ x : Coord, x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) → g x = 0 := by
  -- Step 2: `g = 0` a.e. on each translated strip.
  have hstrip : ∀ k : ℤ, ∀ᵐ x : Coord, 0 < x.1 → c * ((k : ℝ) - 1 / 2) < x.2.1 →
      x.2.1 < c * ((k : ℝ) + 1 / 2) → g x = 0 := by
    intro k
    have hF := (hrBox_qShift_mp (((-k : ℤ) : ℝ) * c)).quasiMeasurePreserving.ae
      (p := fun y : Coord => y ∈ (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) →
        g y = 0) A0
    filter_upwards [hF, per_int hper (-k)] with x h1 h2 hxpos hlo hhi
    have hmem : qShift (((-k : ℤ) : ℝ) * c) x ∈
        (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) := by
      refine ⟨hxpos, ?_, trivial⟩
      have e1 : c * ((k : ℝ) - 1 / 2) = c * k - c / 2 := by ring
      have e2 : c * ((k : ℝ) + 1 / 2) = c * k + c / 2 := by ring
      rw [e1] at hlo
      rw [e2] at hhi
      show -c / 2 < x.2.1 + ((-k : ℤ) : ℝ) * c ∧ x.2.1 + ((-k : ℤ) : ℝ) * c < c / 2
      push_cast
      constructor <;> linarith
    exact (h2 hxpos).symm.trans (h1 hmem)
  -- Step 3: the complement of the strips is null.
  have hNull : ∀ᵐ x : Coord, ∀ k : ℤ, x.2.1 ≠ c * ((k : ℝ) - 1 / 2) := by
    rw [ae_all_iff]
    intro k
    rw [ae_iff]
    have hset : {x : Coord | ¬ (x.2.1 ≠ c * ((k : ℝ) - 1 / 2))} =
        univ ×ˢ (({c * ((k : ℝ) - 1 / 2)} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
      ext x
      simp
    rw [hset]
    simp [Measure.volume_eq_prod, Measure.prod_prod]
  -- Step 4: assemble.
  filter_upwards [ae_all_iff.2 hstrip, hNull] with x hxk hxN hxmem
  have hpos : 0 < x.1 := hxmem.1
  have hfl1 : ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) ≤ x.2.1 / c + 1 / 2 := Int.floor_le _
  have hfl2 : x.2.1 / c + 1 / 2 < ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have lo : c * (((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2) ≤ x.2.1 := by
    have h1 : ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2 ≤ x.2.1 / c := by linarith
    have h2 := (le_div_iff₀ hc).1 h1
    linarith
  have hi : x.2.1 < c * (((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2) := by
    have h1 : x.2.1 / c < ((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2 := by linarith
    have h2 := (div_lt_iff₀ hc).1 h1
    linarith
  have lo' : c * (((⌊x.2.1 / c + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2) < x.2.1 :=
    lt_of_le_of_ne lo (fun h => hxN ⌊x.2.1 / c + 1 / 2⌋ (by linarith [h]))
  exact hxk _ hpos lo' hi

end ProfileStripHelp

open ProfileStripHelp in
/-- **Leaf `PartII-b:G4/3/5/3`** (SP 1902-1906): from the window strip to all of `H_p`. -/
theorem profileStripExtend : UnforcedLeray.Short.IIb.ProfileStripExtend := by
  intro c b b' hc hb hb' hstrip
  have hS0 : MeasurableSet (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) :=
    measurableSet_Ioi.prod (measurableSet_Ioo.prod MeasurableSet.univ)
  have hbp : ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x := QPerHalf.ae_imp hb.periodic
  have hbp' : ∀ᵐ x : Coord, 0 < x.1 → b' (qShift c x) = b' x := QPerHalf.ae_imp hb'.periodic
  -- Per component: `b_j = b'_j` a.e. on `s > 0`.
  have hpt : ∀ j : Fin 2, ∀ᵐ x : Coord, 0 < x.1 → b x j = b' x j := by
    intro j
    have hgper : ∀ᵐ x : Coord, 0 < x.1 → (fun y : Coord => b y j - b' y j) (qShift c x) =
        (fun y : Coord => b y j - b' y j) x := by
      filter_upwards [hbp, hbp'] with x h1 h2 hx0
      simp only [h1 hx0, h2 hx0]
    have A0 : ∀ᵐ x : Coord, x ∈ (Ioi (0 : ℝ) ×ˢ (Ioo (-c / 2) (c / 2) ×ˢ (univ : Set ℝ))) →
        (fun y : Coord => b y j - b' y j) x = 0 := by
      filter_upwards [(ae_restrict_iff' hS0).1 (hstrip j)] with x hx hxS
      have h := hx hxS
      have hpos : (0 : ℝ) < x.1 := hxS.1
      have hne : ((Real.sqrt x.1 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hpos).ne'
      exact (mul_eq_zero.1 h).resolve_left hne
    filter_upwards [strip_all hc hgper A0] with x hx hpos
    have := hx (show x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) from ⟨hpos, trivial⟩)
    exact sub_eq_zero.1 this
  -- Combined: `b = b'` a.e. on `s > 0`.
  have hbb : ∀ᵐ x : Coord, 0 < x.1 → b x = b' x := by
    filter_upwards [hpt 0, hpt 1] with x h0 h1 hpos
    ext j
    fin_cases j
    · exact h0 hpos
    · exact h1 hpos
  -- Transfer to `hMeas c bgp = ageμ c (bgp/2 - 5/2)`, which lives on `s > 0`.
  have hnull : volume {x : Coord | ¬ (0 < x.1 → b x = b' x)} = 0 := ae_iff.1 hbb
  have hM : volume (toMeasurable volume {x : Coord | ¬ (0 < x.1 → b x = b' x)}) = 0 := by
    rw [measure_toMeasurable]
    exact hnull
  have hμ : Axi.ageμ c (bgp / 2 - 5 / 2)
      (toMeasurable volume {x : Coord | ¬ (0 < x.1 → b x = b' x)}) = 0 :=
    ageμ_null_of_volume_null hc (measurableSet_toMeasurable _ _) hM
  have hac : ∀ᵐ x ∂(Axi.ageμ c (bgp / 2 - 5 / 2)), 0 < x.1 → b x = b' x := by
    rw [ae_iff]
    exact measure_mono_null (subset_toMeasurable _ _) hμ
  show ∀ᵐ x ∂(Axi.ageμ c (bgp / 2 - 5 / 2)), b x = b' x
  filter_upwards [hac, Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x h1 h2
  exact h1 (show (0 : ℝ) < x.1 from h2.1)

end UnforcedLeray.Short.IIb
