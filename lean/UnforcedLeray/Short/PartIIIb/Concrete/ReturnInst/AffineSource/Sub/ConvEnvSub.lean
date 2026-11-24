import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvGeoSub

/-!
# Sub-statements and assembly of `ConvGEnvelope` (`PartIII-b:C/asrc/ra/9/2/2/13`)

Source of record: `the November 2 reference manuscript`, lines 5040-5044
(`G = cB0(He,h^p) + cB0(v,ke) + ε cB0(He,ke) + cB1(α,β)` is a finite sum of products of the train
band and the lattice envelope), 5034-5039 (chart rules), 2075-2077 (`U_raw`, `H`), 4963-4980
(`ĥ_A`, `k`), 4371 (train band).

Proved here: `convGEnvelope_of`, the finite sum of pointwise product bounds with the constant
`84 |C_T| C_H`, from the pure pointwise lemmas `CB0Bound`, `CB1Bound`, `ZPairBound`, `CKAdd`,
`CKCongr`, `ToMerNorm`, `LatticeAbsorb`, the `s`-differentiability `ConvSDiff`, and
`TrainBand`, `HpPsiEnv`, `ConvProfileEqs`, `ConvDiffParts`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)

/-- Pointwise bound of `cB0` (source 5040-5044): `cAdv F G = DG·F`, `cDiv F ≤ 2‖DF‖`
(`‖ei i‖ ≤ 1`), so `‖cB0 F G‖ ≤ 3(‖DG‖‖F‖ + ‖DF‖‖G‖)`. -/
def CB0Bound : Prop :=
  ∀ (F G : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ),
    ‖cB0 F G s x‖ ≤ 3 * (‖fderiv ℝ (G s) x‖ * ‖F s x‖ + ‖fderiv ℝ (F s) x‖ * ‖G s x‖)

/-- Pointwise bound of `cB1` (source 5040-5044): `‖cB1 F G‖ ≤ 2(‖F‖‖𝒦G‖ + ‖G‖‖𝒦F‖ + ‖F‖‖G‖)`
(components are bounded by the sup norm). -/
def CB1Bound : Prop :=
  ∀ (F G : ℝ → ℝ × ℝ → ℝ × ℝ) (s : ℝ) (x : ℝ × ℝ),
    ‖cB1 F G s x‖ ≤
      2 * (‖F s x‖ * ‖cK G s x‖ + ‖G s x‖ * ‖cK F s x‖ + ‖F s x‖ * ‖G s x‖)

/-- The planar profile `(0, f)` (`H e_z`, `k e_z`): its derivative and `𝒦` are bounded by those of
`f` (`𝒦` acts componentwise and kills the zero component). -/
def ZPairBound : Prop :=
  ∀ (f : ℝ → ℝ × ℝ → ℝ) (s : ℝ) (x : ℝ × ℝ),
    ‖fderiv ℝ (fun y => ((0 : ℝ), f s y)) x‖ ≤ ‖fderiv ℝ (f s) x‖ ∧
    ‖cK (fun s' y => ((0 : ℝ), f s' y)) s x‖ ≤ |Kop f s x|

/-- `𝒦 = η∂_η + 2s∂_s` is additive on profiles differentiable in `x` (at `s`) and in `s`
(at `x`) (source 5034-5044; `fderiv`, `deriv` are linear). -/
def CKAdd : Prop :=
  ∀ (F E : ℝ → ℝ × ℝ → ℝ × ℝ) (ε s : ℝ) (x : ℝ × ℝ),
    DifferentiableAt ℝ (F s) x → DifferentiableAt ℝ (E s) x →
    DifferentiableAt ℝ (fun s' => F s' x) s → DifferentiableAt ℝ (fun s' => E s' x) s →
    cK (fun s' y => F s' y + ε • E s' y) s x = cK F s x + ε • cK E s x

/-- `cK` at `s > 0` only depends on the profile on `s' > 0` (`deriv` is local). -/
def CKCongr : Prop :=
  ∀ (F G : ℝ → ℝ × ℝ → ℝ × ℝ), (∀ s' : ℝ, 0 < s' → ∀ y : ℝ × ℝ, F s' y = G s' y) →
    ∀ (s : ℝ), 0 < s → ∀ x : ℝ × ℝ, cK F s x = cK G s x

/-- `‖(a, b)‖_{ℓ²} ≤ 2 ‖(a, b)‖_{sup}`. -/
def ToMerNorm : Prop := ∀ w : ℝ × ℝ, ‖toMer w‖ ≤ 2 * ‖w‖

/-- Absorbing the polynomial weight into the lattice degree (source 5040-5044):
`(1+|η|)^M Σ_j W_N(x-jc) ≤ Σ_j W_{N+M}(x-jc)` (termwise `(1+|η|)^M ≤ (1+|u|+|η|)³`; both sums
converge for `α > 0`, `c ≥ 1` by the Gaussian). -/
def LatticeAbsorb : Prop :=
  ∀ (α : ℝ), 0 < α → ∀ (M N : ℕ) (c : ℝ), 1 ≤ c → ∀ x : ℝ × ℝ,
    (1 + |x.2|) ^ M * latticeS α N c x ≤ latticeS α (N + M) c x

/-- Differentiability in `s > 0` (at fixed `x`) of the four planar pieces `v`, `He`, `h^p_A`, `ke`
(source 2049, 2075-2077, 4978: the train, its stream and the lattice sums are smooth in `s > 0`
with derivatives summable). -/
def ConvSDiff (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ dm dp : ℝ, 0 < dm → ∀ (p : Params) (d : ℝ),
    UnforcedLeray.Short.IIb.BgRegime p d dm dp → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∀ s : ℝ, 0 < s → ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ (fun s' => trPl p s' x) s ∧ DifferentiableAt ℝ (fun s' => trHe p s' x) s ∧
      DifferentiableAt ℝ (fun s' => hpPl p χf A s' x) s ∧
      DifferentiableAt ℝ (fun s' => kEz p χf A s' x) s

/-- **The envelope of `sG` from the sub-statements.** -/
theorem convGEnvelope_of (as : ℝ) (χf : ℝ → ℝ) (hT : TrainBand) (hH : HpPsiEnv as)
    (hP : ConvProfileEqs as χf) (hDP : ConvDiffParts as χf) (hSD : ConvSDiff as χf)
    (hB0 : CB0Bound) (hB1 : CB1Bound) (hZ : ZPairBound) (hKA : CKAdd) (hKC : CKCongr)
    (hTM : ToMerNorm) (hLA : LatticeAbsorb) : ConvGEnvelope as χf := by
  intro hχ dm dp hdm
  obtain ⟨CT, kT, NT, νT, hνT, HT⟩ := hT dm dp hdm
  obtain ⟨CH, α, N, hCH, hα, HH⟩ := hH
  refine ⟨84 * |CT| * CH, α, N + NT, kT, min νT 1, by positivity, hα, lt_min hνT one_pos,
    fun p d hreg hν A hA s hs hsT x => ?_⟩
  have hν1 : p.ν ≤ νT := hν.trans (min_le_left _ _)
  have hν2 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hε0 : 0 < p.ε := p.ε_pos
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    have : 0 < d := lt_of_lt_of_le hreg.dm_pos hreg.dm_le
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hνpos.le
  have hc1 : 1 ≤ cOf p.ν := by
    unfold cOf
    rw [one_le_inv₀ (by positivity)]
    have := pow_le_one₀ hνpos.le hν2 (n := 2)
    linarith
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := HT p d hreg hν1 s hs hsT x
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := HH χf hχ p.ν hνpos hν2 A hA s hs hsT x
  obtain ⟨d1, d2, d3, d4⟩ := hDP hχ dm dp hdm p d hreg A hA s hs x
  obtain ⟨e1, e2, e3, e4⟩ := hSD hχ dm dp hdm p d hreg A hA s hs x
  set L : ℝ := latticeS α N (cOf p.ν) x with hL
  set M : ℝ := affM p.ν χf A with hM
  have hM0 : 0 ≤ M := affM_nonneg p.ν χf A
  have h52 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  set Tb : ℝ := |CT| * p.ν⁻¹ ^ kT * (1 + |x.2|) ^ NT with hTb
  set Hb : ℝ := CH * M * s ^ (5 / 2 : ℝ) * L with hHb
  have hTb0 : 0 ≤ Tb := by positivity
  have hCT : ∀ y : ℝ, y ≤ CT * p.ν⁻¹ ^ kT * (1 + |x.2|) ^ NT → y ≤ Tb := fun y hy =>
    hy.trans (by
      rw [hTb]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _)
        (by positivity)) (by positivity))
  have hL0 : 0 ≤ L := by
    rw [hL]; unfold latticeS latticeW
    exact tsum_nonneg (fun j => by positivity)
  have hHb0 : 0 ≤ Hb := by positivity
  have f_v : ‖trPl p s x‖ ≤ Tb := hCT _ b1
  have f_Dv : ‖fderiv ℝ (trPl p s) x‖ ≤ Tb := hCT _ b2
  have f_Kv : ‖cK (trPl p) s x‖ ≤ Tb := hCT _ b3
  have f_H : |trH p s x| ≤ Tb := hCT _ b4
  have f_DH : ‖fderiv ℝ (trH p s) x‖ ≤ Tb := hCT _ b5
  have f_KH : |Kop (trH p) s x| ≤ Tb := hCT _ b6
  have g_hp : ‖hpPl p χf A s x‖ ≤ Hb := c1
  have g_Dhp : ‖fderiv ℝ (hpPl p χf A s) x‖ ≤ Hb := c2
  have g_Khp : ‖cK (hpPl p χf A) s x‖ ≤ Hb := c3
  have g_k : |kPl p χf A s x| ≤ Hb := c4
  have g_Dk : ‖fderiv ℝ (kPl p χf A s) x‖ ≤ Hb := c5
  have g_Kk : |Kop (kOf p.ν χf A) s x| ≤ Hb := c6
  have zp : ∀ (f : ℝ → ℝ × ℝ → ℝ) (B : ℝ), 0 ≤ B → |f s x| ≤ B →
      ‖fderiv ℝ (f s) x‖ ≤ B → |Kop f s x| ≤ B →
      ‖((0 : ℝ), f s x)‖ ≤ B ∧ ‖fderiv ℝ (fun y => ((0 : ℝ), f s y)) x‖ ≤ B ∧
        ‖cK (fun s' y => ((0 : ℝ), f s' y)) s x‖ ≤ B := by
    intro f B hB h1 h2 h3
    obtain ⟨z1, z2⟩ := hZ f s x
    refine ⟨?_, z1.trans h2, z2.trans h3⟩
    rw [Prod.norm_def]
    exact max_le (by simpa using hB) (by simpa [Real.norm_eq_abs] using h1)
  obtain ⟨n1, n2, n3⟩ := zp (trH p) Tb hTb0 f_H f_DH f_KH
  obtain ⟨m1, m2, m3⟩ := zp (kPl p χf A) Hb hHb0 g_k g_Dk g_Kk
  have n_He : ‖trHe p s x‖ ≤ Tb := n1
  have n_DHe : ‖fderiv ℝ (trHe p s) x‖ ≤ Tb := n2
  have n_KHe : ‖cK (trHe p) s x‖ ≤ Tb := n3
  have m_ke : ‖kEz p χf A s x‖ ≤ Hb := m1
  have m_Dke : ‖fderiv ℝ (kEz p χf A s) x‖ ≤ Hb := m2
  have m_Kke : ‖cK (kEz p χf A) s x‖ ≤ Hb := m3
  have hεs : ∀ (w : ℝ × ℝ) (B : ℝ), ‖w‖ ≤ B → ‖p.ε • w‖ ≤ B := by
    intro w B h
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
    calc p.ε * ‖w‖ ≤ 1 * B := mul_le_mul hε1 h (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have hrawK : cK (rawPl p) s x = cK (trPl p) s x + p.ε • cK (trHe p) s x := by
    have h1 := hKC (rawPl p) (fun s' y => trPl p s' y + p.ε • trHe p s' y)
      (fun s' hs' y => (hP p A s' hs' y).1) s hs x
    rw [h1]; exact hKA (trPl p) (trHe p) p.ε s x d1 d2 e1 e2
  have hhatK : cK (hatPl p χf A) s x =
      cK (hpPl p χf A) s x + p.ε • cK (kEz p χf A) s x := by
    have h1 := hKC (hatPl p χf A) (fun s' y => hpPl p χf A s' y + p.ε • kEz p χf A s' y)
      (fun s' hs' y => (hP p A s' hs' y).2) s hs x
    rw [h1]; exact hKA (hpPl p χf A) (kEz p χf A) p.ε s x d3 d4 e3 e4
  have r1 : ‖rawPl p s x‖ ≤ 2 * Tb := by
    rw [(hP p A s hs x).1]
    calc _ ≤ ‖trPl p s x‖ + ‖p.ε • trHe p s x‖ := norm_add_le _ _
      _ ≤ Tb + Tb := add_le_add f_v (hεs _ _ n_He)
      _ = _ := by ring
  have r2 : ‖cK (rawPl p) s x‖ ≤ 2 * Tb := by
    rw [hrawK]
    calc _ ≤ ‖cK (trPl p) s x‖ + ‖p.ε • cK (trHe p) s x‖ := norm_add_le _ _
      _ ≤ Tb + Tb := add_le_add f_Kv (hεs _ _ n_KHe)
      _ = _ := by ring
  have r3 : ‖hatPl p χf A s x‖ ≤ 2 * Hb := by
    rw [(hP p A s hs x).2]
    calc _ ≤ ‖hpPl p χf A s x‖ + ‖p.ε • kEz p χf A s x‖ := norm_add_le _ _
      _ ≤ Hb + Hb := add_le_add g_hp (hεs _ _ m_ke)
      _ = _ := by ring
  have r4 : ‖cK (hatPl p χf A) s x‖ ≤ 2 * Hb := by
    rw [hhatK]
    calc _ ≤ ‖cK (hpPl p χf A) s x‖ + ‖p.ε • cK (kEz p χf A) s x‖ := norm_add_le _ _
      _ ≤ Hb + Hb := add_le_add g_Khp (hεs _ _ m_Kke)
      _ = _ := by ring
  have t1 : ‖cB0 (trHe p) (hpPl p χf A) s x‖ ≤ 6 * (Tb * Hb) := by
    refine (hB0 _ _ s x).trans ?_
    have := mul_le_mul g_Dhp n_He (norm_nonneg _) hHb0
    have := mul_le_mul n_DHe g_hp (norm_nonneg _) hTb0
    linarith
  have t2 : ‖cB0 (trPl p) (kEz p χf A) s x‖ ≤ 6 * (Tb * Hb) := by
    refine (hB0 _ _ s x).trans ?_
    have := mul_le_mul m_Dke f_v (norm_nonneg _) hHb0
    have := mul_le_mul f_Dv m_ke (norm_nonneg _) hTb0
    linarith
  have t3 : ‖p.ε • cB0 (trHe p) (kEz p χf A) s x‖ ≤ 6 * (Tb * Hb) := by
    refine hεs _ _ ((hB0 _ _ s x).trans ?_)
    have := mul_le_mul m_Dke n_He (norm_nonneg _) hHb0
    have := mul_le_mul n_DHe m_ke (norm_nonneg _) hTb0
    linarith
  have t4 : ‖cB1 (rawPl p) (hatPl p χf A) s x‖ ≤ 24 * (Tb * Hb) := by
    refine (hB1 _ _ s x).trans ?_
    have := mul_le_mul r1 r4 (norm_nonneg _) (by positivity)
    have := mul_le_mul r3 r2 (norm_nonneg _) (by positivity)
    have := mul_le_mul r1 r3 (norm_nonneg _) (by positivity)
    linarith
  have hG : ‖convG p χf A s x‖ ≤ 42 * (Tb * Hb) := by
    unfold convG
    have q1 := norm_add_le (cB0 (trHe p) (hpPl p χf A) s x + cB0 (trPl p) (kEz p χf A) s x +
      p.ε • cB0 (trHe p) (kEz p χf A) s x) (cB1 (rawPl p) (hatPl p χf A) s x)
    have q2 := norm_add_le (cB0 (trHe p) (hpPl p χf A) s x + cB0 (trPl p) (kEz p χf A) s x)
      (p.ε • cB0 (trHe p) (kEz p χf A) s x)
    have q3 := norm_add_le (cB0 (trHe p) (hpPl p χf A) s x) (cB0 (trPl p) (kEz p χf A) s x)
    linarith
  have h72 : s ^ (7 / 2 : ℝ) = s * s ^ (5 / 2 : ℝ) := by
    have : (7 / 2 : ℝ) = 1 + 5 / 2 := by norm_num
    rw [this, Real.rpow_add hs, Real.rpow_one]
  calc ‖s • toMer (convG p χf A s x)‖ = s * ‖toMer (convG p χf A s x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    _ ≤ s * (2 * (42 * (Tb * Hb))) :=
        mul_le_mul_of_nonneg_left ((hTM _).trans (by linarith)) hs.le
    _ = (84 * |CT| * CH) * p.ν⁻¹ ^ kT * M * s ^ (7 / 2 : ℝ) * ((1 + |x.2|) ^ NT * L) := by
        rw [hTb, hHb, h72]; ring
    _ ≤ (84 * |CT| * CH) * p.ν⁻¹ ^ kT * M * s ^ (7 / 2 : ℝ) *
          latticeS α (N + NT) (cOf p.ν) x :=
        mul_le_mul_of_nonneg_left (hLA α hα NT N _ hc1 x) (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete
