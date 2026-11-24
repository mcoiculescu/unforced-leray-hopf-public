import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4

/-!
# Part II-b, task `PartII-b:T12/1/4/1` (`PPLSequence`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1933-1935
("applying the Euclidean estimate to a cutoff of `N` repeated cells, dividing its `r`-th power by
`N`, and letting `N → ∞`").

Construction: `F_N = ppCut c N F` (the indicator of `0 ≤ q < N c` times `F`), `G_N` the planar
Helmholtz companion of `F_N` from `PlaneHelmholtzLr` (constant `C_pl`), and
`H_N = ppAvg c N G_N = N⁻¹ Σ_{|j| ≤ N} G_N(· + j c e_q)`; the target constant is `3 C_pl`.

Leaves (`PPLCutNorm`, `PPLAvgBound`, `PPLAvgDivFree`, `PPLAvgTelescope`, `PPLAvgDual`,
`PPLDualLimit`).  Proved here: `pplSequence_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The cut `F_N = 1_{0 ≤ q < N c} F`. -/
def ppCut (c : ℝ) (N : ℕ) (F : ℝ × ℝ → CMerid) : ℝ × ℝ → CMerid :=
  Set.indicator {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 < (N : ℝ) * c} F

/-- The translate average `H_N = N⁻¹ Σ_{|j| ≤ N} G(· + j c e_q)`. -/
def ppAvg (c : ℝ) (N : ℕ) (G : ℝ × ℝ → CMerid) : ℝ × ℝ → CMerid := fun z =>
  ((N : ℂ)⁻¹) • ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (z.1 + (j : ℝ) * c, z.2)

/-- The dual average `N⁻¹ Σ_{|j| ≤ N} Ψ(· - j c e_q)` of a real planar field. -/
def ppDual (c : ℝ) (N : ℕ) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (z : ℝ × ℝ) (i : Fin 2) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Ψ (z.1 - (j : ℝ) * c, z.2) i

/-- **Leaf `PartII-b:T12/1/4/1/1`** (SP 1933-1935): the cut of a `c`-periodic `L^p` field lies in
`L^p(ℝ²)` with `‖F_N‖_p^p = N c ‖F‖_{L^p(avgμ c)}^p` (the cell `[0, N c)` is `N` periods, and
`avgμ c = c⁻¹ dq dη` on one period; integrals of periodic functions over any period agree). -/
def PPLCutNorm : Prop :=
  ∀ c : ℝ, 0 < c → ∀ p : ℝ, 0 < p → ∀ F : ℝ × ℝ → CMerid, CylLp c p F → ∀ N : ℕ,
    MemLp (ppCut c N F) (ENNReal.ofReal p) volume ∧
      eLpNorm (ppCut c N F) (ENNReal.ofReal p) volume =
        ENNReal.ofReal ((N : ℝ) * c) ^ (1 / p) *
          eLpNorm F (ENNReal.ofReal p) (UnforcedLeray.Cyl.avgμ c)

/-- **Leaf `PartII-b:T12/1/4/1/2`** (SP 1933-1935): window bound for the translate average.
By Minkowski, `‖H‖_{p,W} ≤ N⁻¹ Σ_j ‖G(· + j c e_q)‖_{p,W}`; by Hölder over the `≤ 2N+1`
translates `‖H‖_{p,W}^p ≤ N⁻ᵖ (2N+1)^{p-1} Σ_j ∫_{W + j c} |G|^p`; the windows `W + jc` (`W` of
width `2Mc`) overlap at most `2M` times, so `Σ_j ∫_{W+jc}|G|^p ≤ 2M ‖G‖_p^p ≤ 2M (N c) A^p`; and
`(2N+1) ≤ 3N` for `N ≥ 1` gives `‖H‖_{p,W} ≤ 3^{(p-1)/p} (2Mc)^{1/p} A ≤ 3 (2Mc)^{1/p} A`.
(`N = 0`: `H = 0`.) Measurability of the finite sum of translates: `MemLp.comp_measurePreserving`
for `(q, η) ↦ (q + j c, η)`. -/
def PPLAvgBound : Prop :=
  ∀ c : ℝ, 0 < c → ∀ p : ℝ, 1 ≤ p → ∀ (G : ℝ × ℝ → CMerid) (N M : ℕ) (A : ℝ≥0∞),
    MemLp G (ENNReal.ofReal p) volume →
    eLpNorm G (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ((N : ℝ) * c) ^ (1 / p) * A →
      MemLp (ppAvg c N G) (ENNReal.ofReal p) (volume.restrict (ppWindow c M)) ∧
        eLpNorm (ppAvg c N G) (ENNReal.ofReal p) (volume.restrict (ppWindow c M)) ≤
          3 * ENNReal.ofReal (2 * (M : ℝ) * c) ^ (1 / p) * A

/-- **Leaf `PartII-b:T12/1/4/1/3`** (SP 1933-1935): if `G ∈ L²(ℝ²)` is weakly divergence free
against planar tests, so is each translate (`φ(· - jc e_q)` is a planar test and Lebesgue measure is
translation invariant; integrability from `L²` times a compactly supported smooth gradient), hence
`ppAvg c N G` (a finite combination), with the integral exactly `0`. -/
def PPLAvgDivFree : Prop :=
  ∀ (c : ℝ) (N : ℕ) (G : ℝ × ℝ → CMerid), MemLp G 2 volume →
    (∀ φ : ℝ × ℝ → ℝ, PlaneTest φ →
      ∫ z, (G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = 0) →
    ∀ φ : ℝ × ℝ → ℝ, PlaneTest φ →
      ∫ z, (ppAvg c N G z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
        ppAvg c N G z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = 0

/-- **Leaf `PartII-b:T12/1/4/1/4`** (SP 1933-1935, "no period loss"): telescoping,
`H(z + c e_q) - H(z) = N⁻¹ (G(z + (N+1) c e_q) - G(z - N c e_q))`, so on any window its `L²` norm
is at most `N⁻¹ (‖G‖₂ + ‖G‖₂)` (translation invariance of Lebesgue measure). -/
def PPLAvgTelescope : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (G : ℝ × ℝ → CMerid), MemLp G 2 volume → ∀ N M : ℕ, 1 ≤ N →
    eLpNorm (fun z : ℝ × ℝ => ppAvg c N G (z.1 + c, z.2) - ppAvg c N G z) 2
      (volume.restrict (ppWindow c M)) ≤ 2 * ENNReal.ofReal ((N : ℝ)⁻¹) * eLpNorm G 2 volume

/-- **Leaf `PartII-b:T12/1/4/1/5`** (SP 1933-1935): moving the translates onto the test:
if `G` is a planar Helmholtz companion of the cut `F_N` of a `c`-periodic `L²` field `F`, `G ∈ L²`,
and `Ψ` a planar solenoidal test, then
`∫ (F - H_N)·Ψ = ∫ F·Ψ - ∫ F_N · (N⁻¹ Σ_j Ψ(· - jc e_q))`.
Proof: `∫ G(· + jc)·Ψ = ∫ G·Ψ(· - jc)` (translation), `Ψ(· - jc)` is again a planar solenoidal
test, so `∫ (F_N - G)·Ψ(· - jc) = 0` by `IsPlaneHelmholtz`; sum over `j`, then `∫ (F - F_N)Ψ`
is `∫ FΨ - ∫ F_N Ψ`, and `∫ F_N Ψ`-term is part of the `j = 0` summand bookkeeping
(`F` locally `L²`, `Ψ` compactly supported, so all pairings are integrable). -/
def PPLAvgDual : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (N : ℕ) (F G : ℝ × ℝ → CMerid) (Ψ : ℝ × ℝ → Fin 2 → ℝ),
    CylLp c 2 F → MemLp G 2 volume → IsPlaneHelmholtz (ppCut c N F) G → PlaneSolTest Ψ →
      ∫ z, ∑ i : Fin 2, (F z i - ppAvg c N G z i) * (Ψ z i : ℂ) =
        (∫ z, ∑ i : Fin 2, F z i * (Ψ z i : ℂ)) -
          ∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ)

/-- **Leaf `PartII-b:T12/1/4/1/6`** (SP 1933-1935): the Riemann-sum limit.  For `c`-periodic
`F ∈ L²_loc` and a planar test `Ψ` supported in `|q| ≤ K c`: for `N > 2K` the translates
`Ψ(· - jc)` with `K < j < N - K` are supported in `0 ≤ q < N c`, where `F_N = F`, and by periodicity
`∫ F·Ψ(· - jc) = ∫ F·Ψ`; the other `O(K)` values of `j` (`|j| ≤ N`) contribute at most
`O(K) N⁻¹ · ‖F‖_{L²(window)}‖Ψ‖_∞`-type terms (j < 0 contribute `0`; there are `N - O(K)` good `j`),
so `∫ F_N · ppDual Ψ → ∫ F·Ψ` as `N → ∞`. -/
def PPLDualLimit : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (F : ℝ × ℝ → CMerid) (Ψ : ℝ × ℝ → Fin 2 → ℝ),
    CylLp c 2 F → PlaneSolTest Ψ →
      Tendsto (fun N : ℕ => ∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ)) atTop
        (𝓝 (∫ z, ∑ i : Fin 2, F z i * (Ψ z i : ℂ)))

/-- The real bound `2 N⁻¹ (N c)^{1/2} → 0`. -/
theorem ppl_rate_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => 2 * (N : ℝ)⁻¹ * ((N : ℝ) * c) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have h2 := (h1.const_mul (2 * c ^ (1 / (2 : ℝ))))
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.mul_rpow hN0.le hc.le, Real.rpow_neg hN0.le]
  have : (N : ℝ) = (N : ℝ) ^ (1 / (2 : ℝ)) * (N : ℝ) ^ (1 / (2 : ℝ)) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hp : 0 < (N : ℝ) ^ (1 / (2 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hinv : (N : ℝ)⁻¹ = ((N : ℝ) ^ (1 / (2 : ℝ)) * (N : ℝ) ^ (1 / (2 : ℝ)))⁻¹ := by
    rw [← this]
  rw [hinv]
  field_simp

theorem pplSequence_of (h1 : PPLCutNorm) (h2 : PPLAvgBound) (h3 : PPLAvgDivFree)
    (h4 : PPLAvgTelescope) (h5 : PPLAvgDual) (h6 : PPLDualLimit) (hPl : PlaneHelmholtzLr) :
    PPLSequence := by
  intro r hr
  obtain ⟨Cp, hCp, hG⟩ := hPl r hr
  refine ⟨3 * Cp, by positivity, ?_⟩
  intro c hc F hF hF2
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have e2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  have key : ∀ N : ℕ, ∃ G : ℝ × ℝ → CMerid, MemLp G 2 volume ∧
      MemLp G (ENNReal.ofReal r) volume ∧
      eLpNorm G 2 volume ≤ ENNReal.ofReal ((N : ℝ) * c) ^ (1 / (2 : ℝ)) *
        eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c) ∧
      eLpNorm G (ENNReal.ofReal r) volume ≤ ENNReal.ofReal ((N : ℝ) * c) ^ (1 / r) *
        (ENNReal.ofReal Cp * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) ∧
      IsPlaneHelmholtz (ppCut c N F) G := by
    intro N
    obtain ⟨m2, n2⟩ := h1 c hc 2 two_pos F hF2 N
    obtain ⟨mr, nr⟩ := h1 c hc r hr0 F hF N
    rw [e2] at m2 n2
    obtain ⟨G, hG2, hGr, hn2, hnr, hH⟩ := hG _ m2 mr
    refine ⟨G, hG2, hGr, ?_, ?_, hH⟩
    · exact hn2.trans (le_of_eq n2)
    · refine hnr.trans (le_of_eq ?_)
      rw [nr]; ring
  choose G hG2 hGr hn2 hnr hHel using key
  have a2 : ∀ N M : ℕ, MemLp (ppAvg c N (G N)) 2 (volume.restrict (ppWindow c M)) ∧
      eLpNorm (ppAvg c N (G N)) 2 (volume.restrict (ppWindow c M)) ≤
        3 * ENNReal.ofReal (2 * (M : ℝ) * c) ^ (1 / (2 : ℝ)) *
          eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c) := by
    intro N M
    have := h2 c hc 2 (by norm_num) (G N) N M (eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c))
      (by rw [e2]; exact hG2 N) (by rw [e2]; exact hn2 N)
    rw [e2] at this
    exact this
  have ar : ∀ N M : ℕ, MemLp (ppAvg c N (G N)) (ENNReal.ofReal r)
        (volume.restrict (ppWindow c M)) ∧
      eLpNorm (ppAvg c N (G N)) (ENNReal.ofReal r) (volume.restrict (ppWindow c M)) ≤
        3 * ENNReal.ofReal (2 * (M : ℝ) * c) ^ (1 / r) *
          (ENNReal.ofReal Cp * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) :=
    fun N M => h2 c hc r hr.le (G N) N M _ (hGr N) (hnr N)
  refine ⟨fun N => ppAvg c N (G N), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N M
    exact ⟨(a2 N M).1, (ar N M).1⟩
  · intro N M
    refine (ar N M).2.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (p := 3) (q := Cp) (by norm_num), ENNReal.ofReal_ofNat]
    ring
  · intro N M
    exact (a2 N M).2
  · intro M
    have hA : eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c) ≠ ⊤ := by
      have := hF2.2
      rw [e2] at this
      exact this.eLpNorm_ne_top
    have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (2 * (N : ℝ)⁻¹ * ((N : ℝ) * c) ^ (1 / (2 : ℝ))) *
        eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_ofReal (ppl_rate_tendsto c hc))) (Or.inr hA)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    calc eLpNorm (fun z : ℝ × ℝ => ppAvg c N (G N) (z.1 + c, z.2) - ppAvg c N (G N) z) 2
          (volume.restrict (ppWindow c M))
        ≤ 2 * ENNReal.ofReal ((N : ℝ)⁻¹) * eLpNorm (G N) 2 volume := h4 c hc (G N) (hG2 N) N M hN
      _ ≤ 2 * ENNReal.ofReal ((N : ℝ)⁻¹) * (ENNReal.ofReal ((N : ℝ) * c) ^ (1 / (2 : ℝ)) *
          eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c)) := by gcongr; exact hn2 N
      _ = ENNReal.ofReal (2 * (N : ℝ)⁻¹ * ((N : ℝ) * c) ^ (1 / (2 : ℝ))) *
          eLpNorm F 2 (UnforcedLeray.Cyl.avgμ c) := by
        rw [ENNReal.ofReal_mul (p := 2 * (N : ℝ)⁻¹) (by positivity),
          ENNReal.ofReal_mul (p := 2) (by norm_num),
          ← ENNReal.ofReal_rpow_of_nonneg (x := (N : ℝ) * c) (by positivity) (by norm_num),
          ENNReal.ofReal_ofNat]
        ring
  · intro φ hφ
    have := fun N : ℕ => h3 c N (G N) (hG2 N) (fun ψ hψ => ((hHel N).1 ψ hψ).2) φ hφ
    exact (tendsto_const_nhds (x := (0 : ℂ))).congr (fun N => (this N).symm)
  · intro Ψ hΨ
    have e : ∀ N : ℕ, (∫ z, ∑ i : Fin 2, (F z i - ppAvg c N (G N) z i) * (Ψ z i : ℂ)) =
        (∫ z, ∑ i : Fin 2, F z i * (Ψ z i : ℂ)) -
          ∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ) :=
      fun N => h5 c hc N F (G N) Ψ hF2 (hG2 N) (hHel N) hΨ
    have := (tendsto_const_nhds (x := ∫ z, ∑ i : Fin 2, F z i * (Ψ z i : ℂ))).sub
      (h6 c hc F Ψ hF2 hΨ)
    rw [sub_self] at this
    exact this.congr (fun N => (e N).symm)

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.pplSequence_of
