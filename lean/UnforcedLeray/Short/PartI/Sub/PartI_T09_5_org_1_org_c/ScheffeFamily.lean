import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.JetSum

/-!
# `PartI:T09/5/org/1/org/c/5`: the vector Scheffe lemma in `L^2(A)` at age `0`

Source: `the November 2 reference manuscript`,
lines 270-288 (the `L^2` convergence at age `0` of the word derivatives of the train).

This is the finite-family version of `scheffeL2At0_proof` (task `c/4`), proved directly (route B).
Writing `B = ∫_A Σ_i F_i(0)^2`, `a_s = ∫_A Σ_i F_i(s)^2`, `D_s = ∫_A Σ_i (F_i(s) - F_i(0))^2` and
`P_s = ∫_A Σ_i (F_i(s) + F_i(0))^2`, the pointwise identity
`(x-y)^2 + (x+y)^2 = 2x^2 + 2y^2`, summed over `i`, gives `D_s + P_s = 2 a_s + 2 B`.
Fatou's lemma along `𝓝[≥] 0` (applied to the summed integrand, whose pointwise limit is
`4 Σ_i F_i(0)^2`) gives `4 B ≤ liminf P_s`, and `limsup a_s ≤ B` is the hypothesis.  Hence
`limsup D_s = 0`, and each single term `∫_A (F_i(s) - F_i(0))^2` is at most `D_s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **Vector Scheffe lemma in `L²` along `s → 0+`** (see `ScheffeL2FamilyAt0`). -/
theorem scheffeL2FamilyAt0_proof : ScheffeL2FamilyAt0 := by
  intro ι I A F hA hcont hpt hfin hlim
  set u : Filter ℝ := nhdsWithin (0 : ℝ) (Ici 0) with hu_def
  have sqm : ∀ g : Plane → ℝ, Continuous g → Measurable (fun z => ENNReal.ofReal ((g z) ^ 2)) :=
    fun g hg => ((hg.pow 2).measurable).ennreal_ofReal
  have hmB : Measurable (fun z => ∑ i ∈ I, ENNReal.ofReal ((F i 0 z) ^ 2)) :=
    Finset.measurable_sum I (fun i hi => sqm (F i 0) (hcont i hi 0 le_rfl))
  -- the total at age `0`
  set B : ℝ≥0∞ := ∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i 0 z) ^ 2) with hB_def
  have hBfin : B < ⊤ := by
    rw [hB_def, lintegral_finsetSum I (fun i hi => sqm (F i 0) (hcont i hi 0 le_rfl))]
    exact ENNReal.sum_lt_top.2 (fun i hi => hfin i hi)
  -- the limsup hypothesis in the summed form
  have hlim' : limsup (fun s : ℝ => ∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) u ≤ B := by
    have e : (fun s : ℝ => ∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) =
        fun s : ℝ => ∫⁻ z in A, ENNReal.ofReal (∑ i ∈ I, (F i s z) ^ 2) := by
      funext s
      apply lintegral_congr
      intro z
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    have e0 : ∫⁻ z in A, ENNReal.ofReal (∑ i ∈ I, (F i 0 z) ^ 2) = B := by
      rw [hB_def]
      apply lintegral_congr
      intro z
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    rw [e, ← e0]
    exact hlim
  -- pointwise identity, summed over the family
  have hpt_id : ∀ (x y : ι → ℝ),
      ∑ i ∈ I, ENNReal.ofReal ((x i - y i) ^ 2) + ∑ i ∈ I, ENNReal.ofReal ((x i + y i) ^ 2) =
        2 * ∑ i ∈ I, ENNReal.ofReal ((x i) ^ 2) + 2 * ∑ i ∈ I, ENNReal.ofReal ((y i) ^ 2) := by
    intro x y
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h2 : ∀ r : ℝ, (2 : ℝ≥0∞) * ENNReal.ofReal r = ENNReal.ofReal (2 * r) := fun r => by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    have e1 : ENNReal.ofReal ((x i - y i) ^ 2) + ENNReal.ofReal ((x i + y i) ^ 2) =
        ENNReal.ofReal ((x i - y i) ^ 2 + (x i + y i) ^ 2) :=
      (ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)).symm
    have e2 : 2 * ENNReal.ofReal ((x i) ^ 2) + 2 * ENNReal.ofReal ((y i) ^ 2) =
        ENNReal.ofReal (2 * (x i) ^ 2 + 2 * (y i) ^ 2) := by
      rw [h2, h2, ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 2 * (x i) ^ 2)
        (by positivity : (0 : ℝ) ≤ 2 * (y i) ^ 2)]
    rw [e1, e2]
    congr 1
    ring
  -- the energy identity `D_s + P_s = 2 a_s + 2 B`
  have hid : ∀ s : ℝ, 0 ≤ s →
      (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) +
        (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) =
      2 * (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) + 2 * B := by
    intro s hs
    have hm1 : Measurable (fun z => ∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) :=
      Finset.measurable_sum I (fun i hi =>
        sqm (fun z => F i s z - F i 0 z) ((hcont i hi s hs).sub (hcont i hi 0 le_rfl)))
    have hm2 : Measurable (fun z => ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) :=
      Finset.measurable_sum I (fun i hi =>
        sqm (fun z => F i s z + F i 0 z) ((hcont i hi s hs).add (hcont i hi 0 le_rfl)))
    have hmA : Measurable (fun z => ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) :=
      Finset.measurable_sum I (fun i hi => sqm (F i s) (hcont i hi s hs))
    calc (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) +
          (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2))
        = ∫⁻ z in A, (∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2) +
            ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) :=
          (lintegral_add_left (μ := volume.restrict A) hm1 _).symm
      _ = ∫⁻ z in A, (2 * ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2) +
            2 * ∑ i ∈ I, ENNReal.ofReal ((F i 0 z) ^ 2)) :=
          lintegral_congr fun z => hpt_id (fun i => F i s z) (fun i => F i 0 z)
      _ = (∫⁻ z in A, 2 * ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) +
            ∫⁻ z in A, 2 * ∑ i ∈ I, ENNReal.ofReal ((F i 0 z) ^ 2) :=
          lintegral_add_left (μ := volume.restrict A) (hmA.const_mul 2) _
      _ = 2 * (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) + 2 * B := by
          rw [lintegral_const_mul (μ := volume.restrict A) _ hmA,
            lintegral_const_mul (μ := volume.restrict A) _ hmB, hB_def]
  -- Fatou along `u`: `4 B ≤ liminf P_s`
  have hfatou : 4 * B ≤ liminf (fun s : ℝ => ∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) u := by
    obtain ⟨G, hG⟩ : ∃ G : ℝ → Plane → ℝ≥0∞,
        G = fun s z => if 0 ≤ s then ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2) else 0 :=
      ⟨_, rfl⟩
    have hGm : ∀ s : ℝ, Measurable (G s) := by
      intro s
      by_cases hs : 0 ≤ s
      · have e : G s = fun z => ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2) := by
          rw [hG]; funext z; simp only [↓reduceIte, hs]
        rw [e]
        exact Finset.measurable_sum I (fun i hi =>
          sqm (fun z => F i s z + F i 0 z) ((hcont i hi s hs).add (hcont i hi 0 le_rfl)))
      · have e : G s = fun _ => 0 := by
          rw [hG]; funext z; simp only [↓reduceIte, hs]
        rw [e]
        exact measurable_const
    have hpt_lim : ∀ z : Plane,
        Tendsto (fun s : ℝ => G s z) u (𝓝 (∑ i ∈ I, ENNReal.ofReal ((F i 0 z + F i 0 z) ^ 2))) := by
      intro z
      have h1 : Tendsto (fun s : ℝ => ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) u
          (𝓝 (∑ i ∈ I, ENNReal.ofReal ((F i 0 z + F i 0 z) ^ 2))) := by
        apply tendsto_finsetSum
        intro i hi
        have h2 : Tendsto (fun s : ℝ => F i s z + F i 0 z) u (𝓝 (F i 0 z + F i 0 z)) :=
          (hpt i hi z).add tendsto_const_nhds
        exact (ENNReal.continuous_ofReal.tendsto _).comp (h2.pow 2)
      refine Tendsto.congr' ?_ h1
      filter_upwards [eventually_nhdsWithin_of_forall (fun s (hs : s ∈ Ici (0 : ℝ)) => hs)]
        with s hs
      have hs' : 0 ≤ s := hs
      rw [hG]
      simp only [↓reduceIte, hs']
    have hfatou' := lintegral_liminf_le' (μ := volume.restrict A) (u := u) (f := G)
      (fun s => (hGm s).aemeasurable)
    have hL : ∫⁻ z in A, liminf (fun s : ℝ => G s z) u =
        ∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i 0 z + F i 0 z) ^ 2) :=
      lintegral_congr fun z => (hpt_lim z).liminf_eq
    have hR : liminf (fun s : ℝ => ∫⁻ z in A, G s z) u =
        liminf (fun s : ℝ => ∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) u := by
      apply Filter.liminf_congr
      filter_upwards [eventually_nhdsWithin_of_forall (fun s (hs : s ∈ Ici (0 : ℝ)) => hs)]
        with s hs
      have hs' : 0 ≤ s := hs
      apply lintegral_congr
      intro z
      rw [hG]
      simp only [↓reduceIte, hs']
    have h4 : ∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i 0 z + F i 0 z) ^ 2) = 4 * B := by
      have hpt4 : ∀ z : Plane,
          ∑ i ∈ I, ENNReal.ofReal ((F i 0 z + F i 0 z) ^ 2) =
            4 * ∑ i ∈ I, ENNReal.ofReal ((F i 0 z) ^ 2) := by
        intro z
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have e : (F i 0 z + F i 0 z) ^ 2 = 4 * (F i 0 z) ^ 2 := by ring
        rw [e, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
      rw [lintegral_congr hpt4, lintegral_const_mul (μ := volume.restrict A) _ hmB, hB_def]
    rw [← h4, ← hL, ← hR]
    exact hfatou'
  -- the eventual bounds
  have hmemu : ∀ᶠ s in u, 0 ≤ s := eventually_nhdsWithin_of_forall (fun s hs => hs)
  -- the summed Scheffe bound: `D_s ≤ δ` eventually
  have key : ∀ δ : ℝ≥0∞, 0 < δ → ∀ᶠ s in u,
      (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) ≤ δ := by
    intro δ hδ
    by_cases hδtop : δ = ⊤
    · exact Filter.Eventually.of_forall fun s => by rw [hδtop]; exact le_top
    have hδ' : δ ≠ ⊤ := hδtop
    obtain ⟨η, hη_def⟩ : ∃ η : ℝ≥0∞, η = δ * 3⁻¹ := ⟨_, rfl⟩
    have h3ne : (3 : ℝ≥0∞) ≠ 0 := by norm_num
    have h3top : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have hη0 : η ≠ 0 := by
      rw [hη_def]; exact mul_ne_zero hδ.ne' (ENNReal.inv_ne_zero.2 h3top)
    have hηtop : η ≠ ⊤ := by
      rw [hη_def]; exact ENNReal.mul_ne_top hδ' (ENNReal.inv_ne_top.2 h3ne)
    have h3η : 3 * η = δ := by
      rw [hη_def, ← mul_assoc, mul_comm (3 : ℝ≥0∞) δ, mul_assoc,
        ENNReal.mul_inv_cancel h3ne h3top, mul_one]
    -- eventually `a_s < B + η`
    have hA : ∀ᶠ s in u, (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) < B + η :=
      Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim' (ENNReal.lt_add_right hBfin.ne hη0))
    -- eventually `4 B ≤ P_s + η`
    have hP : ∀ᶠ s in u, 4 * B ≤
        (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) + η := by
      by_cases h4 : 4 * B = 0
      · exact Filter.Eventually.of_forall fun s => by simp [h4]
      · have hlt : 4 * B - η < 4 * B :=
          ENNReal.sub_lt_self (ENNReal.mul_ne_top (by norm_num) hBfin.ne) h4 hη0
        have hev := Filter.eventually_lt_of_lt_liminf (hlt.trans_le hfatou)
        filter_upwards [hev] with s hs
        exact le_tsub_add.trans (add_le_add hs.le le_rfl)
    filter_upwards [hA, hP, hmemu] with s hAs hPs hs
    have hAle : (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) ≤ B + η := hAs.le
    have hid_s := hid s hs
    have ha_fin : (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) < ⊤ :=
      hAs.trans (ENNReal.add_lt_top.2 ⟨hBfin, lt_top_iff_ne_top.2 hηtop⟩)
    have hsum : (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) +
        (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) < ⊤ := by
      rw [hid_s]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) ha_fin,
        ENNReal.mul_lt_top (by norm_num) hBfin⟩
    have hPfin : (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) ≠ ⊤ :=
      (lt_of_le_of_lt le_add_self hsum).ne
    have hle : (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) +
        (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) ≤
        3 * η + (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) := by
      rw [hid_s]
      calc 2 * (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z) ^ 2)) + 2 * B
          ≤ 2 * (B + η) + 2 * B := by gcongr
        _ = 4 * B + 2 * η := by ring
        _ ≤ ((∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) + η) + 2 * η := by
          gcongr
        _ = 3 * η + (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z + F i 0 z) ^ 2)) := by ring
    have hDle : (∫⁻ z in A, ∑ i ∈ I, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) ≤ 3 * η :=
      ENNReal.le_of_add_le_add_right hPfin hle
    exact hDle.trans h3η.le
  -- conclusion, term by term
  intro i hi
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  filter_upwards [key δ hδ] with s hs
  have hsingle : (∫⁻ z in A, ENNReal.ofReal ((F i s z - F i 0 z) ^ 2)) ≤
      ∫⁻ z in A, ∑ j ∈ I, ENNReal.ofReal ((F j s z - F j 0 z) ^ 2) := by
    apply lintegral_mono
    intro z
    exact Finset.single_le_sum (f := fun j => ENNReal.ofReal ((F j s z - F j 0 z) ^ 2))
      (fun j _ => zero_le) hi
  exact hsingle.trans hs

end UnforcedLeray.Short.PartI
