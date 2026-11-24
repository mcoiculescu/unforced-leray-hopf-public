import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerMulDeriv

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2/5`: the kernel term has its age derivative on `[a, b)`

Ico transcription of `Interior/TimeJets/KerMulDeriv.lean` (`kerMulDeriv`, Ioo); only the

the November 2 reference manuscript` 3052-3058, 3060-3061.  As for the Ioo version the bound
`KerAdjXBound m` is available for `m > 1` only (the source uses `m > 8`, SP 2826, 3123), so the
statement carries `1 < m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

open Set

/-- **The kernel term has its age derivative** (SP 3052-3058, `m > 1`). -/
theorem kerMulDerivIco (m : ℝ) (hm : 1 < m) : KerMulDerivIco m := by
  unfold KerMulDerivIco
  intro c a b G G' f f' hc hG hG' hGd hf hf' hfX
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  obtain ⟨K, hK0, hK⟩ := weightedMulL12 c m hc0
  obtain ⟨CX, hCX0, hCX⟩ := kerAdjXBound m hm
  -- the fields `G(r) f(r)` are in `L¹ ∩ L²` of the cell
  have KA : ∀ (Gx : ℝ → Fin 2 → ℝ × ℝ → ℝ) (fx : ℝ → ℝ × ℝ → ℂ) (r0 : ℝ),
      IsWeightedCoeff c m (Ico a b) Gx → r0 ∈ Ico a b →
      MemLp (fx r0) 2 (B0579.cellMeasure c (-m)) → KmL12 c (kmH Gx fx r0) := by
    intro Gx fx r0 hGx hr0 hfx
    unfold KmL12
    intro l
    obtain ⟨C0, hC0⟩ := (hGx.2 [] l r0 hr0).1
    have hmeas : AEStronglyMeasurable (Gx r0 l) (volume.restrict (B0579.cell c)) :=
      ((hGx.1 r0 hr0 l).1.continuous).aestronglyMeasurable
    obtain ⟨h1, h2, -⟩ := hK (Gx r0 l) (fx r0) C0 hmeas hfx (fun x _ => hC0 x)
    exact ⟨h1, h2⟩
  unfold HasXDerivOn
  intro r hr
  have hsub : 𝓝[Ico a b \ {r}] r ≤ 𝓝[Ico a b] r := nhdsWithin_mono r diff_subset
  have hGc : ∀ l : Fin 2, ∀ ε : ℝ, 0 < ε → ∀ᶠ r' in 𝓝[Ico a b \ {r}] r, ∀ x : ℝ × ℝ,
      ejWeight m x * |G r' l x - G r l x| ≤ ε := fun l ε hε =>
    Filter.Eventually.filter_mono hsub ((hG.2 [] l r hr).2 ε hε)
  have hGb : ∀ l : Fin 2, ∃ C0 : ℝ, ∀ᶠ r' in 𝓝[Ico a b \ {r}] r, ∀ x : ℝ × ℝ,
      ejWeight m x * |G r' l x| ≤ C0 := by
    intro l
    obtain ⟨C1, hC1⟩ := (hG.2 [] l r hr).1
    refine ⟨C1 + 1, ?_⟩
    filter_upwards [hGc l 1 one_pos] with r' hr' x
    have h1 := hr' x
    have h2 := hC1 x
    have hw : 0 ≤ ejWeight m x := by unfold ejWeight; positivity
    have h3 : |G r' l x| ≤ |G r' l x - G r l x| + |G r l x| := by
      have := abs_add_le (G r' l x - G r l x) (G r l x)
      simpa using this
    calc ejWeight m x * |G r' l x|
        ≤ ejWeight m x * (|G r' l x - G r l x| + |G r l x|) := mul_le_mul_of_nonneg_left h3 hw
      _ = ejWeight m x * |G r' l x - G r l x| + ejWeight m x * |G r l x| := by ring
      _ ≤ 1 + C1 := add_le_add h1 h2
      _ ≤ C1 + 1 := by linarith
  choose C0 hC0 using hGb
  have hQ : Tendsto (fun r' => xNorm c (-m) (kmQ f f' r r')) (𝓝[Ico a b \ {r}] r) (𝓝 0) :=
    hfX r hr
  -- the coefficient tails are small
  have hh1 : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 (K * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := ENNReal.tendsto_ofReal h0
    simpa using this
  have hfin1 : xNorm c (-m) (f' r) ≠ ⊤ := (hf' r hr).eLpNorm_lt_top.ne
  have hfin2 : xNorm c (-m) (f r) ≠ ⊤ := (hf r hr).eLpNorm_lt_top.ne
  have hεT : Tendsto (fun ε : ℝ => ENNReal.ofReal CX * ∑ l : Fin 2,
      (ENNReal.ofReal (K * ε) * xNorm c (-m) (f' r) + ENNReal.ofReal (K * ε) * xNorm c (-m) (f r)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h3 : Tendsto (fun ε : ℝ => ENNReal.ofReal (K * ε) * xNorm c (-m) (f' r)
        + ENNReal.ofReal (K * ε) * xNorm c (-m) (f r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have e1 := ENNReal.Tendsto.mul_const hh1 (Or.inr hfin1)
      have e2 := ENNReal.Tendsto.mul_const hh1 (Or.inr hfin2)
      have := e1.add e2
      rw [zero_mul, zero_mul, add_zero] at this
      exact this
    have h4 := tendsto_finset_sum (Finset.univ : Finset (Fin 2)) (fun _ _ => h3)
    have h5 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal CX) h4 (Or.inr ENNReal.ofReal_ne_top)
    rw [Finset.sum_const_zero, mul_zero] at h5
    exact h5
  have hQT : Tendsto (fun r' => ENNReal.ofReal CX * ∑ l : Fin 2,
      ENNReal.ofReal (K * C0 l) * xNorm c (-m) (kmQ f f' r r')) (𝓝[Ico a b \ {r}] r) (𝓝 0) := by
    have h3 : ∀ l : Fin 2, Tendsto (fun r' => ENNReal.ofReal (K * C0 l)
        * xNorm c (-m) (kmQ f f' r r')) (𝓝[Ico a b \ {r}] r) (𝓝 0) := fun l => by
      have e := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (K * C0 l)) hQ (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_zero] at e
      exact e
    have h4 := tendsto_finset_sum (Finset.univ : Finset (Fin 2)) (fun l _ => h3 l)
    have h5 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal CX) h4 (Or.inr ENNReal.ofReal_ne_top)
    rw [Finset.sum_const_zero, mul_zero] at h5
    exact h5
  show Tendsto (fun r' => xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) *
      (kerAdj c (kmH G f r') x - kerAdj c (kmH G f r) x)
      - (kerAdj c (kmH G' f r) x + kerAdj c (kmH G f' r) x))) (𝓝[Ico a b \ {r}] r) (𝓝 0)
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : (0 : ℝ≥0∞) < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨ε, hε, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal CX * ∑ l : Fin 2,
      (ENNReal.ofReal (K * ε) * xNorm c (-m) (f' r) + ENNReal.ofReal (K * ε) * xNorm c (-m) (f r))
        < δ / 2 := by
    have hev := ((tendsto_order.1 hεT).2 (δ / 2) hδ2).and
      (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))
    obtain ⟨ε, h1, h2⟩ := hev.exists
    exact ⟨ε, h2, h1⟩
  have hQ' := (tendsto_order.1 hQT).2 (δ / 2) hδ2
  filter_upwards [hQ', eventually_all.2 (fun l => (hC0 l)),
    eventually_all.2 (fun l => hGc l ε hε), eventually_all.2 (fun l => hGd l r hr ε hε),
    self_mem_nhdsWithin] with r' hq hC0r hGcr hGdr hmem
  have hr'I : r' ∈ Ico a b := hmem.1
  have hfr' : MemLp (f r') 2 (B0579.cellMeasure c (-m)) := hf r' hr'I
  have hfr : MemLp (f r) 2 (B0579.cellMeasure c (-m)) := hf r hr
  have hf'r : MemLp (f' r) 2 (B0579.cellMeasure c (-m)) := hf' r hr
  have hKH' : KmL12 c (kmH G f r') := KA G f r' hG hr'I hfr'
  have hKH : KmL12 c (kmH G f r) := KA G f r hG hr hfr
  have hKA : KmL12 c (kmH G' f r) := KA G' f r hG' hr hfr
  have hKB : KmL12 c (kmH G f' r) := KA G f' r hG hr hf'r
  have hQm : MemLp (kmQ f f' r r') 2 (B0579.cellMeasure c (-m)) :=
    (MemLp.const_mul (hfr'.sub hfr) (((r' - r)⁻¹ : ℝ) : ℂ)).sub hf'r
  have hid := km_ae_identity hc (kmH G f r') (kmH G f r) (kmH G' f r) (kmH G f' r)
    hKH' hKH hKA hKB ((r' - r)⁻¹)
  have hae : (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (kerAdj c (kmH G f r') x - kerAdj c (kmH G f r) x)
      - (kerAdj c (kmH G' f r) x + kerAdj c (kmH G f' r) x)) =ᵐ[B0579.cellMeasure c (-m)]
      kerAdj c (kmX3 G G' f f' r r' ((r' - r)⁻¹)) :=
    (B0579.cellMeasure_ac c (-m)).ae_le hid
  have hxe : xNorm c (-m) (fun x => (((r' - r)⁻¹ : ℝ) : ℂ) * (kerAdj c (kmH G f r') x
      - kerAdj c (kmH G f r) x) - (kerAdj c (kmH G' f r) x + kerAdj c (kmH G f' r) x))
      = xNorm c (-m) (kerAdj c (kmX3 G G' f f' r r' ((r' - r)⁻¹))) := by
    unfold xNorm
    exact eLpNorm_congr_ae hae
  have hX3 : KmL12 c (kmX3 G G' f f' r r' ((r' - r)⁻¹)) :=
    km_comb (km_comb (km_comb hKH' hKH _ _) hKA 1 (-1)) hKB 1 (-1)
  have hbd := hCX c hc _ hX3
  -- the pointwise decomposition of the field
  have hT_eq : ∀ l : Fin 2, kmX3 G G' f f' r r' ((r' - r)⁻¹) l = fun y =>
      (G r' l y : ℂ) * kmQ f f' r r' y + (((G r' l y - G r l y : ℝ)) : ℂ) * f' r y
        + ((((r' - r)⁻¹ * (G r' l y - G r l y) - G' r l y : ℝ)) : ℂ) * f r y := by
    intro l
    funext y
    simp only [kmX3, kmH, kmQ]
    push_cast
    ring
  have hsum_l : ∀ l : Fin 2,
      eLpNorm (kmX3 G G' f f' r r' ((r' - r)⁻¹) l) 1 (volume.restrict (B0579.cell c))
        + eLpNorm (kmX3 G G' f f' r r' ((r' - r)⁻¹) l) 2 (volume.restrict (B0579.cell c))
      ≤ ENNReal.ofReal (K * C0 l) * xNorm c (-m) (kmQ f f' r r')
        + (ENNReal.ofReal (K * ε) * xNorm c (-m) (f' r)
          + ENNReal.ofReal (K * ε) * xNorm c (-m) (f r)) := by
    intro l
    rw [hT_eq l]
    obtain ⟨i1, mm1, bd1⟩ := hK (fun y => G r' l y) (kmQ f f' r r') (C0 l)
      ((hG.1 r' hr'I l).1.continuous.aestronglyMeasurable) hQm (fun x _ => hC0r l x)
    obtain ⟨i2, mm2, bd2⟩ := hK (fun y => G r' l y - G r l y) (f' r) ε
      (((hG.1 r' hr'I l).1.continuous.sub (hG.1 r hr l).1.continuous).aestronglyMeasurable)
      hf'r (fun x _ => hGcr l x)
    obtain ⟨i3, mm3, bd3⟩ := hK (fun y => (r' - r)⁻¹ * (G r' l y - G r l y) - G' r l y) (f r) ε
      ((((continuous_const.mul ((hG.1 r' hr'I l).1.continuous.sub
        (hG.1 r hr l).1.continuous))).sub (hG'.1 r hr l).1.continuous)).aestronglyMeasurable
      hfr (fun x _ => hGdr l x)
    have h1 := km_eLp_tri (μ := volume.restrict (B0579.cell c)) le_rfl _ _ _
      mm1.aestronglyMeasurable mm2.aestronglyMeasurable mm3.aestronglyMeasurable
    have h2 := km_eLp_tri (μ := volume.restrict (B0579.cell c)) (p := 2) (by norm_num) _ _ _
      mm1.aestronglyMeasurable mm2.aestronglyMeasurable mm3.aestronglyMeasurable
    calc _ ≤ _ := add_le_add h1 h2
      _ = _ := by ring
      _ ≤ _ := add_le_add (add_le_add bd1 bd2) bd3
      _ = _ := add_assoc _ _ _
  have hfinal : xNorm c (-m) (kerAdj c (kmX3 G G' f f' r r' ((r' - r)⁻¹))) ≤
      ENNReal.ofReal CX * ∑ l : Fin 2, ENNReal.ofReal (K * C0 l) * xNorm c (-m) (kmQ f f' r r')
      + ENNReal.ofReal CX * ∑ l : Fin 2,
        (ENNReal.ofReal (K * ε) * xNorm c (-m) (f' r) + ENNReal.ofReal (K * ε) * xNorm c (-m) (f r)) := by
    calc _ ≤ ENNReal.ofReal CX * ∑ l : Fin 2, (eLpNorm (kmX3 G G' f f' r r' ((r' - r)⁻¹) l) 1
            (volume.restrict (B0579.cell c))
          + eLpNorm (kmX3 G G' f f' r r' ((r' - r)⁻¹) l) 2 (volume.restrict (B0579.cell c))) := hbd.2
      _ ≤ ENNReal.ofReal CX * ∑ l : Fin 2, (ENNReal.ofReal (K * C0 l) * xNorm c (-m) (kmQ f f' r r')
            + (ENNReal.ofReal (K * ε) * xNorm c (-m) (f' r)
              + ENNReal.ofReal (K * ε) * xNorm c (-m) (f r))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hsum_l l) zero_le
      _ = _ := by rw [Finset.sum_add_distrib, mul_add]
  rw [hxe]
  calc _ ≤ _ := hfinal
    _ ≤ δ / 2 + δ / 2 := add_le_add hq.le hεlt.le
    _ = δ := ENNReal.add_halves δ

end UnforcedLeray.Short.IIIa
