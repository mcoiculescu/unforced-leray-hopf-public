import UnforcedLeray.Lib.PlanarSpectralB.SimpleProj

/-!
# G2 on `𝒳_{0,M}`: the complement bound of the Euler evolution (INF10 target G-5)


§5, Level G, target **G-5** (G2 on `𝒳_{0,M}`:
`∀ η > 0, ∃ C, ∀ t ≥ 0, ‖eulerSemigroup hM t ∘L (1 - 𝒫)‖ ≤ C exp(ηt)`); decision D7 of
`scoping/README.md` (G1 and G2 at `j = 0`, sector by sector, bounded generators). Manuscript
(`paper/main.tex`): Theorem G2 `thm:ref-planar-complement`, `eq:st18-t00010` (lines 707–717,
1547–1580, unit `B0103`), the Riesz projection `𝒫` onto the growing pair (lines 1390–1400,
unit `B0083`), and the complement bound `eq:st18-t00072` (lines 1547–1559, unit `B0100`; the
mass coordinate of lines 1561–1567, unit `B0101`, is the stationary sector `0`).

Construction: `growingProjW P₂ Pm = ⊕ₙ Pₙ` with `P_{±2}` the simple spectral projections of
G-4 in sectors `±2` and `Pₙ = 0` otherwise; `growingProj` is its restriction to `𝒳_{0,M}`
(it maps `L²_M` into `𝒳_{0,M}`, since sector `0` carries the mass). Then
`e^{t𝓛}(1 - 𝒫) = ⊕ₙ exp(t𝓛ₙ)(1 - Pₙ)` and the sector bounds of `SimpleProj.lean` are uniform in
`n`: for `|n|` large, `‖Kₙ‖ ≤ η` (`tendsto_norm_couplingSec`) and the skew transport gives
`‖exp(t𝓛ₙ)‖ ≤ e^{ηt}`; the finitely many remaining sectors use the spectral bounds.

Main declarations (namespace `UnforcedLeray.Planar`): `secProjFam`, `growingProjW`,
`secProf_growingProjW`, `growingProjW_apply`, `growingProjW_mem_X0`, `growingProj`,
`growingProjW_idem`, `growingProjW_rankOne_apply`, `norm_eulerGroupW_comp_le`, `norm_eulerSemigroup_comp_le`,
`exists_uniform_sector_bound`, **`eulerSemigroup_complement_bound`** (G-5).

**Inputs.** The growing mode `(λ, q)` of sector `2` (Prop. `gaussian-existence`, INF18 part of
block 3F) enters as hypotheses `Lsec hM 2 q = λ • q`, `q ≠ 0`, `Re λ > 0`; sector `-2` is its
conjugate (`Lsec_star_eigen`). The sectors `±1` use the named hypothesis `SectorOneStable hM`
(target O13).

**Not built here** (G-5 items of the scoping note): the uniformity in the frozen dilations
`a ∈ [1, A]` (unit `B0102`; needs the dilation conjugacy of target P7,
`𝓛_a = a⁻²J_a𝓛J_a⁻¹`, not built), and
the real-rank-two statement (only the complex range formula `growingProjW_rankOne_apply` is
given).

Status: draft; Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Planar

open UnforcedLeray.Infra.Dunford (IsSimpleSpectralProj rankOneProj)

/-! ### The growing projection -/

/-- The sector family of the growing projection: `P₂` in sector `2`, `Pm` in sector `-2`, `0`
elsewhere. -/
def secProjFam {M : ℝ} (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M) (n : ℤ) : ProfL2 M →L[ℂ] ProfL2 M :=
  if n = 2 then P₂ else if n = -2 then Pm else 0

theorem norm_secProjFam_le {M : ℝ} (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M) (n : ℤ) :
    ‖secProjFam P₂ Pm n‖ ≤ ‖P₂‖ + ‖Pm‖ := by
  unfold secProjFam
  split_ifs
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)
  · rw [norm_zero]
    positivity

/-- **The Riesz projection onto the growing pair**, `𝒫 = ⊕ₙ Pₙ` on `L²_M`. -/
def growingProjW {M : ℝ} (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M) : L2w M →L[ℂ] L2w M :=
  sectorSum (secProjFam P₂ Pm) (norm_secProjFam_le P₂ Pm) (by positivity)

theorem secProf_growingProjW {M : ℝ} (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M) (f : L2w M) (n : ℤ) :
    secProf M n (growingProjW P₂ Pm f) = secProjFam P₂ Pm n (secProf M n f) :=
  secProf_sectorSum _ _ _ f n

/-- `𝒫 f = P₂ f₂ e^{2iϑ} + Pm f₋₂ e^{-2iϑ}`: the range of `𝒫` lies in sectors `±2` (and is
spanned by `q e^{2iϑ}`, `q̄ e^{-2iϑ}` when `P₂, Pm` are the rank-one projections of G-4). -/
theorem growingProjW_apply {M : ℝ} (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M) (f : L2w M) :
    growingProjW P₂ Pm f =
      secEmb M 2 (P₂ (secProf M 2 f)) + secEmb M (-2) (Pm (secProf M (-2) f)) := by
  apply eq_of_secProf
  intro n
  rw [secProf_growingProjW, map_add, secProf_secEmb, secProf_secEmb]
  unfold secProjFam
  by_cases h2 : n = 2
  · subst h2
    simp
  · by_cases h2' : n = -2
    · subst h2'
      simp
    · rw [if_neg h2, if_neg h2', if_neg (Ne.symm h2), if_neg (Ne.symm h2'),
        ContinuousLinearMap.zero_apply, add_zero]

/-- `𝒫` maps `L²_M` into `𝒳_{0,M}`: sector `0` carries the mass and `P₀ = 0`. -/
theorem growingProjW_mem_X0 {M : ℝ} (hM : 1 < M) (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M)
    (f : L2w M) : growingProjW P₂ Pm f ∈ X0 hM := by
  show massCLM hM (growingProjW P₂ Pm f) = 0
  have h0 : secProjFam P₂ Pm 0 = 0 := by
    unfold secProjFam
    rw [if_neg (by decide), if_neg (by decide)]
  rw [massCLM_eq_secEmb_zero, secProf_growingProjW, h0, ContinuousLinearMap.zero_apply, map_zero,
    map_zero]

/-- The growing projection on `𝒳_{0,M}`. -/
def growingProj {M : ℝ} (hM : 1 < M) (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M) : X0 hM →L[ℂ] X0 hM :=
  Infra.ExpSemigroup.restrictOp (growingProjW P₂ Pm) (X0 hM)
    (fun f _ => growingProjW_mem_X0 hM P₂ Pm f)

/-- `𝒫` is a projection when `P₂` and `Pm` are. -/
theorem growingProjW_idem {M : ℝ} {P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M} (h₂ : P₂ * P₂ = P₂)
    (hmm : Pm * Pm = Pm) : growingProjW P₂ Pm ∘L growingProjW P₂ Pm = growingProjW P₂ Pm := by
  ext1 f
  apply eq_of_secProf
  intro n
  rw [ContinuousLinearMap.comp_apply, secProf_growingProjW, secProf_growingProjW,
    ← ContinuousLinearMap.mul_apply]
  unfold secProjFam
  split_ifs
  · rw [h₂]
  · rw [hmm]
  · rw [mul_zero]

/-! ### The complement bound -/

/-- `e^{t𝓛}(1 - 𝒫) = ⊕ₙ exp(t𝓛ₙ)(1 - Pₙ)`, hence its norm is the supremum of the sector norms. -/
theorem norm_eulerGroupW_comp_le {M : ℝ} (hM : 1 < M) (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M)
    (t : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ n, ‖expSec hM t n * (1 - secProjFam P₂ Pm n)‖ ≤ K) :
    ‖eulerGroupW hM t ∘L (1 - growingProjW P₂ Pm)‖ ≤ K := by
  have e : eulerGroupW hM t ∘L (1 - growingProjW P₂ Pm) =
      sectorSum (fun n => expSec hM t n * (1 - secProjFam P₂ Pm n)) hA hK := by
    ext1 f
    apply eq_of_secProf
    intro n
    simp only [ContinuousLinearMap.comp_apply, secProf_eulerGroupW, secProf_sectorSum,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub,
      secProf_growingProjW, ContinuousLinearMap.mul_apply]
  rw [e]
  exact norm_sectorSum_le _ _ _

theorem mapsTo_X0_eulerGroupW_comp {M : ℝ} (hM : 1 < M) (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M)
    (t : ℝ) : ∀ f ∈ X0 hM, (eulerGroupW hM t ∘L (1 - growingProjW P₂ Pm)) f ∈ X0 hM := by
  intro f hf
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]
  exact eulerGroupW_mem_X0 hM t _ (Submodule.sub_mem _ hf (growingProjW_mem_X0 hM P₂ Pm f))

/-- The restriction to `𝒳_{0,M}` does not increase the norm. -/
theorem norm_eulerSemigroup_comp_le {M : ℝ} (hM : 1 < M) (P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M)
    (t : ℝ) : ‖eulerSemigroup hM t ∘L (1 - growingProj hM P₂ Pm)‖ ≤
      ‖eulerGroupW hM t ∘L (1 - growingProjW P₂ Pm)‖ := by
  have e : eulerSemigroup hM t ∘L (1 - growingProj hM P₂ Pm) =
      Infra.ExpSemigroup.restrictOp (eulerGroupW hM t ∘L (1 - growingProjW P₂ Pm)) (X0 hM)
        (mapsTo_X0_eulerGroupW_comp hM P₂ Pm t) := by
    ext1 f
    apply Subtype.ext
    simp only [ContinuousLinearMap.comp_apply, coe_eulerSemigroup_apply,
      Infra.ExpSemigroup.coe_restrictOp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, Submodule.coe_sub, growingProj]
  rw [e]
  exact Infra.ExpSemigroup.norm_restrictOp_le _ _ _

/-- **Uniform sector bounds**: for every `η > 0` there is one `C` with
`‖exp(t𝓛ₙ)(1 - Pₙ)‖ ≤ C e^{ηt}` for all sectors `n` and `t ≥ 0`. -/
theorem exists_uniform_sector_bound {M : ℝ} (hM : 1 < M) (h1 : SectorOneStable hM) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM 2 q = z₀ • q)
    {P₂ Pm : ProfL2 M →L[ℂ] ProfL2 M} (hP₂ : IsSimpleSpectralProj (Lsec hM 2) P₂ z₀)
    (hPm : IsSimpleSpectralProj (Lsec hM (-2)) Pm (conj z₀)) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (t : ℝ), 0 ≤ t →
      ‖expSec hM t n * (1 - secProjFam P₂ Pm n)‖ ≤ C * Real.exp (η * t) := by
  have hsec : ∀ n : ℤ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖expSec hM t n * (1 - secProjFam P₂ Pm n)‖ ≤ C * Real.exp (η * t) := by
    intro n
    by_cases h2 : n = 2
    · subst h2
      rw [secProjFam, if_pos rfl]
      exact exists_norm_expSec_mul_one_sub_le hM (by decide) hz₀ hq0 hq hP₂ hη
    · by_cases h2' : n = -2
      · subst h2'
        rw [secProjFam, if_neg (by decide), if_pos rfl]
        have hre : 0 < (conj z₀).re := by rw [Complex.conj_re]; exact hz₀
        exact exists_norm_expSec_mul_one_sub_le hM (by decide) hre (star_ne_zero_prof hq0)
          (Lsec_star_eigen hM hq) hPm hη
      · rw [secProjFam, if_neg h2, if_neg h2', sub_zero]
        simp only [mul_one]
        have hn : n.natAbs ≠ 2 := by
          intro h
          rcases Int.natAbs_eq_iff.1 h with h | h
          · exact h2 (by simpa using h)
          · exact h2' (by simpa using h)
        exact exists_norm_expSec_le_of_ne_two hM h1 hn hη
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ‖couplingSec hM (k : ℤ)‖ ≤ η :=
    Filter.eventually_atTop.1 ((tendsto_norm_couplingSec hM).eventually (ge_mem_nhds hη))
  choose Cf hCf0 hCf using hsec
  set S : Finset ℤ := Finset.Icc (-(N : ℤ) - 3) ((N : ℤ) + 3) with hS
  have hsum0 : 0 ≤ ∑ n ∈ S, Cf n := Finset.sum_nonneg fun n _ => (hCf0 n).le
  refine ⟨1 + ∑ n ∈ S, Cf n, by positivity, fun n t ht => ?_⟩
  have hexp : 0 < Real.exp (η * t) := Real.exp_pos _
  by_cases hn : n ∈ S
  · calc ‖expSec hM t n * (1 - secProjFam P₂ Pm n)‖ ≤ Cf n * Real.exp (η * t) := hCf n t ht
      _ ≤ (1 + ∑ n ∈ S, Cf n) * Real.exp (η * t) := by
        gcongr
        calc Cf n ≤ ∑ n ∈ S, Cf n :=
              Finset.single_le_sum (f := Cf) (fun i _ => (hCf0 i).le) hn
          _ ≤ 1 + ∑ n ∈ S, Cf n := le_add_of_nonneg_left zero_le_one
  · rw [hS, Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    have hn2 : n ≠ 2 := by omega
    have hn2' : n ≠ -2 := by omega
    rw [secProjFam, if_neg hn2, if_neg hn2', sub_zero, mul_one]
    have hcpl : ‖couplingSec hM n‖ ≤ η := by
      rcases le_or_gt 0 n with h0 | h0
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
        exact hN k (by omega)
      · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat h0.le
        rw [couplingSec_neg, norm_neg]
        exact hN k (by omega)
    calc ‖expSec hM t n‖ ≤ Real.exp (t * ‖couplingSec hM n‖) :=
          Infra.norm_exp_skew_add_le (adjoint_transportSec M n) ht
      _ ≤ Real.exp (η * t) := by
          rw [mul_comm η t]
          exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hcpl ht)
      _ ≤ (1 + ∑ n ∈ S, Cf n) * Real.exp (η * t) := by
          nlinarith

/-- **G-5** (G2 on `𝒳_{0,M}` at `j = 0`, `eq:st18-t00010`, tex lines 707–717 and 1547–1580):
given the growing mode `𝓛₂ q = λ q` (`q ≠ 0`, `Re λ > 0`) and the `|n| = 1` input
`SectorOneStable`, there are simple spectral projections `P₂` (sector `2`, eigenvalue `λ`) and
`Pm` (sector `-2`, eigenvalue `λ̄`) such that the Riesz projection
`𝒫 = growingProj hM P₂ Pm` onto the growing pair satisfies, for every `η > 0`,
`‖e^{t𝓛}(I - 𝒫)‖_{𝒳_{0,M} → 𝒳_{0,M}} ≤ C e^{ηt}` for all `t ≥ 0`. -/
theorem eulerSemigroup_complement_bound {M : ℝ} (hM : 1 < M) (h1 : SectorOneStable hM)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) {q : ProfL2 M} (hq0 : q ≠ 0) (hq : Lsec hM 2 q = z₀ • q) :
    ∃ ℓ₂ ℓm : ProfL2 M →L[ℂ] ℂ, ℓ₂ q = 1 ∧ ℓm (star q) = 1 ∧
      IsSimpleSpectralProj (Lsec hM 2) (rankOneProj ℓ₂ q) z₀ ∧
      IsSimpleSpectralProj (Lsec hM (-2)) (rankOneProj ℓm (star q)) (conj z₀) ∧
      ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
        ‖eulerSemigroup hM t ∘L
            (1 - growingProj hM (rankOneProj ℓ₂ q) (rankOneProj ℓm (star q)))‖ ≤
          C * Real.exp (η * t) := by
  obtain ⟨ℓ₂, h₂, -, hP₂⟩ := exists_isSimpleSpectralProj_Lsec_two hM (m := 2) (by decide) hz₀ hq0 hq
  have hre : 0 < (conj z₀).re := by rw [Complex.conj_re]; exact hz₀
  obtain ⟨ℓm, hm, -, hPm⟩ := exists_isSimpleSpectralProj_Lsec_two hM (m := -2) (by decide) hre
    (star_ne_zero_prof hq0) (Lsec_star_eigen hM hq)
  refine ⟨ℓ₂, ℓm, h₂, hm, hP₂, hPm, fun η hη => ?_⟩
  obtain ⟨C, hC, hCb⟩ := exists_uniform_sector_bound hM h1 hz₀ hq0 hq hP₂ hPm hη
  refine ⟨C, hC, fun t ht => ?_⟩
  exact (norm_eulerSemigroup_comp_le hM _ _ t).trans
    (norm_eulerGroupW_comp_le hM _ _ t (by positivity) fun n => hCb n t ht)

/-- **The range of `𝒫` has complex dimension at most two**: with the rank-one projections of
G-4, `𝒫 f = ℓ₂(f₂) q e^{2iϑ} + ℓ₋(f₋₂) q̄ e^{-2iϑ}` (tex lines 1390–1400: "their joint complex
range has dimension two"). -/
theorem growingProjW_rankOne_apply {M : ℝ} (ℓ₂ ℓm : ProfL2 M →L[ℂ] ℂ) (q qm : ProfL2 M)
    (f : L2w M) :
    growingProjW (rankOneProj ℓ₂ q) (rankOneProj ℓm qm) f =
      ℓ₂ (secProf M 2 f) • secEmb M 2 q + ℓm (secProf M (-2) f) • secEmb M (-2) qm := by
  rw [growingProjW_apply, Infra.Dunford.rankOneProj_apply, Infra.Dunford.rankOneProj_apply,
    LinearIsometry.map_smul, LinearIsometry.map_smul]

end UnforcedLeray.Planar
