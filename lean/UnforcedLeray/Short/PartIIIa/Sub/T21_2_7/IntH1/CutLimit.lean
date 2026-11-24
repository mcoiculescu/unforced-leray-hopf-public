import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit

/-!
# `PartIII-a:T21/2/7/2/2/1/3`: the limit passage `AdjCutLimit`

Source: `the November 2 reference manuscript` (SP) lines 3060-3067. Route:
Fatou in `x` along `ladCut (n+1)^2 ↑ 1` (the cut is eventually `1` on each slice), Fatou in `ρ`
on `Ioo r s` (joint measurability via a piecewise extension of the jointly smooth slice
derivative), and monotone convergence for `s' ↑ s` (`setLIntegral_iUnion_of_directed`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

set_option maxHeartbeats 1600000 in
/-- **Leaf `PartIII-a:T21/2/7/2/2/1/3`** (SP 3060-3067): the limit passage. -/
theorem adjCutLimit (m : ℝ) : AdjCutLimit m := by
  classical
  intro ν tr t s G φ hctx K hK r hr k
  obtain ⟨hν, _hν1, _hb, _ht, _hts, _hG, _hW, hC⟩ := hctx
  have hνne : ENNReal.ofReal ν ≠ 0 := (ENNReal.ofReal_pos.2 hν).ne'
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ × (ℝ × ℝ) → ℂ, Q = (Ico t s ×ˢ (univ : Set (ℝ × ℝ))).piecewise
      (fun p : ℝ × (ℝ × ℝ) => pdCx k (φ p.1) p.2) (fun _ => 0) := ⟨_, rfl⟩
  have hP : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => pdCx k (φ p.1) p.2)
      (Ico t s ×ˢ (univ : Set (ℝ × ℝ))) :=
    (jointSmooth_pdCx hC k).continuousOn
  have hQm : Measurable Q := by
    rw [hQdef]
    exact ContinuousOn.measurable_piecewise hP continuousOn_const
      (measurableSet_Ico.prod MeasurableSet.univ)
  have hQeq : ∀ ρ ∈ Ico t s, ∀ x : ℝ × ℝ, Q (ρ, x) = pdCx k (φ ρ) x := by
    intro ρ hρ x
    rw [hQdef]
    exact Set.piecewise_eq_of_mem _ _ _ (⟨hρ, mem_univ x⟩ : (ρ, x) ∈ Ico t s ×ˢ (univ : Set (ℝ × ℝ)))
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ × (ℝ × ℝ) → ℝ≥0∞, ∀ n p, g n p =
      ENNReal.ofReal (ladCut ((n : ℝ) + 1) p.2 ^ 2) * ‖Q p‖ₑ ^ (2 : ℝ) :=
    ⟨fun n p => ENNReal.ofReal (ladCut ((n : ℝ) + 1) p.2 ^ 2) * ‖Q p‖ₑ ^ (2 : ℝ), fun _ _ => rfl⟩
  have hcut : ∀ R : ℝ, Measurable (fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (ladCut R p.2 ^ 2)) := by
    intro R
    have hc : Continuous (fun p : ℝ × (ℝ × ℝ) => ladCut R p.2 ^ 2) :=
      ((CutLimitAux.continuous_cut R).comp continuous_snd).pow 2
    exact ENNReal.measurable_ofReal.comp hc.measurable
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    have e : g n = fun p : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (ladCut ((n : ℝ) + 1) p.2 ^ 2) * ‖Q p‖ₑ ^ (2 : ℝ) := funext (hg n)
    rw [e]
    exact (hcut _).mul (hQm.enorm.pow_const _)
  have hgeq : ∀ n ρ, ρ ∈ Ico t s → ∀ x : ℝ × ℝ, g n (ρ, x) =
      ENNReal.ofReal (ladCut ((n : ℝ) + 1) x ^ 2) * ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ) := by
    intro n ρ hρ x
    rw [hg, hQeq ρ hρ x]
  have hlim : ∀ ρ x, Tendsto (fun n => g n (ρ, x)) atTop (𝓝 (‖Q (ρ, x)‖ₑ ^ (2 : ℝ))) := by
    intro ρ x
    have hev : ∀ᶠ n : ℕ in atTop, |x.2| + 1 ≤ (n : ℝ) + 1 := by
      filter_upwards [eventually_ge_atTop ⌈|x.2|⌉₊] with n hn
      have h1 := Nat.le_ceil |x.2|
      have h2 : ((⌈|x.2|⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev] with n hn
    rw [hg]
    simp [CutLimitAux.eq_one hn]
  have hSF : SFinite (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    unfold B0579.cellMeasure
    infer_instance
  have hJm : ∀ n, Measurable (fun ρ => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) :=
    fun n => Measurable.lintegral_prod_right' (hgm n)
  have hFx : ∀ ρ, ∫⁻ x, ‖Q (ρ, x)‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop := by
    intro ρ
    have h := lintegral_liminf_le' (μ := B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
      (u := atTop) (f := fun n x => g n (ρ, x))
      (fun n => ((hgm n).comp measurable_prodMk_left).aemeasurable)
    calc ∫⁻ x, ‖Q (ρ, x)‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        = ∫⁻ x, liminf (fun n => g n (ρ, x)) atTop ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
          lintegral_congr fun x => ((hlim ρ x).liminf_eq).symm
      _ ≤ _ := h
  have hFp : ∀ ρ ∈ Ioo r s, ∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ≤
      liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop := by
    intro ρ hρ
    have hρ' : ρ ∈ Ico t s := ⟨hr.1.trans hρ.1.le, hρ.2⟩
    have e : ∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) =
        ∫⁻ x, ‖Q (ρ, x)‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
      lintegral_congr fun x => by rw [hQeq ρ hρ' x]
    rw [e]
    exact hFx ρ
  -- the bound on each Fatou term, uniformly over the exhaustion of `Ioo r s`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ≥0∞, D = ENNReal.ofReal K / ENNReal.ofReal ν := ⟨_, rfl⟩
  have hpos : 0 < s - r := sub_pos.2 hr.2
  obtain ⟨sm, hsm⟩ : ∃ sm : ℕ → ℝ, ∀ m' : ℕ, sm m' = s - (s - r) / ((m' : ℝ) + 1) :=
    ⟨fun m' => s - (s - r) / ((m' : ℝ) + 1), fun _ => rfl⟩
  have hsm_lt : ∀ m', sm m' < s := by
    intro m'
    rw [hsm]
    have : 0 < (s - r) / ((m' : ℝ) + 1) := div_pos hpos (by positivity)
    linarith
  have hsm_ge : ∀ m', r ≤ sm m' := by
    intro m'
    rw [hsm]
    have h0 : (0 : ℝ) ≤ (m' : ℝ) := Nat.cast_nonneg m'
    have : (s - r) / ((m' : ℝ) + 1) ≤ s - r := div_le_self hpos.le (by linarith)
    linarith
  have hsm_mono : Monotone sm := by
    intro a b hab
    rw [hsm, hsm]
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    have : (s - r) / ((b : ℝ) + 1) ≤ (s - r) / ((a : ℝ) + 1) :=
      div_le_div_of_nonneg_left hpos.le (by positivity) (by linarith)
    linarith
  have hU : (⋃ m', Ioc r (sm m')) = Ioo r s := by
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨m', h1, h2⟩
      exact ⟨h1, lt_of_le_of_lt h2 (hsm_lt m')⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨m', hm'⟩ := exists_nat_gt ((s - r) / (s - x))
      refine ⟨m', h1, ?_⟩
      rw [hsm]
      have hsx : 0 < s - x := sub_pos.2 h2
      have h3 : s - r < (m' : ℝ) * (s - x) := (div_lt_iff₀ hsx).1 hm'
      have h4 : (s - r) / ((m' : ℝ) + 1) ≤ s - x := by
        rw [div_le_iff₀ (by positivity)]
        have h0 : (0 : ℝ) ≤ (m' : ℝ) := Nat.cast_nonneg m'
        nlinarith
      linarith
  have hmonoS : Monotone (fun m' => Ioc r (sm m')) := fun a b hab => Ioc_subset_Ioc_right (hsm_mono hab)
  have hJbd : ∀ n : ℕ, ∫⁻ ρ in Ioo r s, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
      ≤ D := by
    intro n
    have hterm : ∀ m', ∫⁻ ρ in Ioc r (sm m'), ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        ≤ D := by
      intro m'
      have hI : ∫⁻ ρ in Ioc r (sm m'), ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
          = ∫⁻ ρ in Ioc r (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) φ k ρ := by
        refine setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => ?_)
        have hρ' : ρ ∈ Ico t s := ⟨hr.1.trans hρ.1.le, hρ.2.trans_lt (hsm_lt m')⟩
        exact lintegral_congr fun x => hgeq n ρ hρ' x
      rw [hI, hDdef]
      have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hsub : sm m' ∈ Ico r s := ⟨hsm_ge m', hsm_lt m'⟩
      have h1 := hK ((n : ℝ) + 1) hR r hr (sm m') hsub
      have h2 : ∫⁻ ρ in Ioc r (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) φ k ρ ≤
          ∑ k' : Fin 2, ∫⁻ ρ in Ioc r (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) φ k' ρ :=
        Finset.single_le_sum (f := fun k' : Fin 2 =>
          ∫⁻ ρ in Ioc r (sm m'), cutGradEnergy (ν ^ (-2 : ℝ)) m ((n : ℝ) + 1) φ k' ρ)
          (fun _ _ => zero_le) (Finset.mem_univ k)
      refine (ENNReal.le_div_iff_mul_le (Or.inl hνne) (Or.inl ENNReal.ofReal_ne_top)).2 ?_
      refine (mul_comm _ _).trans_le ?_
      exact le_trans (mul_le_mul_of_nonneg_left h2 zero_le) h1
    have hset : ∫⁻ ρ in Ioo r s, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))
        = ⨆ m', ∫⁻ ρ in Ioc r (sm m'), ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
      rw [← hU]
      exact setLIntegral_iUnion_of_directed _ hmonoS.directed_le
    rw [hset]
    exact iSup_le hterm
  have hIoo : ∫⁻ ρ in Ioc r s, (∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) = ∫⁻ ρ in Ioo r s, (∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) :=
    (setLIntegral_congr Ioo_ae_eq_Ioc).symm
  have h1 : ∫⁻ ρ in Ioo r s, (∫⁻ x, ‖pdCx k (φ ρ) x‖ₑ ^ (2 : ℝ)
      ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) ≤
      ∫⁻ ρ in Ioo r s, liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop :=
    setLIntegral_mono' measurableSet_Ioo (fun ρ hρ => hFp ρ hρ)
  have h2 : ∫⁻ ρ in Ioo r s, liminf (fun n => ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop
      ≤ liminf (fun n => ∫⁻ ρ in Ioo r s, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) atTop :=
    lintegral_liminf_le' (fun n => (hJm n).aemeasurable)
  have h3 : liminf (fun n => ∫⁻ ρ in Ioo r s, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
      atTop ≤ D := by
    calc liminf (fun n => ∫⁻ ρ in Ioo r s, ∫⁻ x, g n (ρ, x) ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)))
          atTop ≤ liminf (fun _ : ℕ => D) atTop := liminf_le_liminf (Eventually.of_forall hJbd)
      _ = D := liminf_const D
  rw [hIoo]
  have hfin : D < ⊤ := by
    rw [hDdef]
    exact ENNReal.div_lt_top ENNReal.ofReal_ne_top hνne
  exact lt_of_le_of_lt (h1.trans (h2.trans h3)) hfin

end UnforcedLeray.Short.IIIa
