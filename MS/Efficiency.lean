import MS.Envelope
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open MeasureTheory

set_option linter.style.haveILetI false

namespace MSData

theorem diag_null (D : MSData) :
    D.mu.prod D.nu {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  letI : NullSingletonClass D.nu := D.nu_noAtoms
  rw [Measure.measure_prod_null
    (measurableSet_eq_fun measurable_fst measurable_snd)]
  apply Filter.Eventually.of_forall
  intro v
  have hpre : Prod.mk v ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {v} := by
    ext c
    simp
  change D.nu (Prod.mk v ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0
  simp [hpre]

theorem q_ae_ind (D : MSData) :
    D.q =ᵐ[D.mu.prod D.nu]
      (fun p => Set.indicator {p : ℝ × ℝ | p.2 < p.1} 1 p) := by
  have hB : ∀ᵐ p ∂(D.mu.prod D.nu), p.2 < p.1 → D.q p = 1 := by
    exact (ae_restrict_iff' (measurableSet_lt measurable_snd measurable_fst)).1 D.effB
  have hS : ∀ᵐ p ∂(D.mu.prod D.nu), p.1 < p.2 → D.q p = 0 := by
    exact (ae_restrict_iff' (measurableSet_lt measurable_fst measurable_snd)).1 D.effS
  have hdiag : ∀ᵐ p ∂(D.mu.prod D.nu), p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa [not_ne_iff] using D.diag_null
  filter_upwards [hB, hS, hdiag] with p hpB hpS hpdiag
  rcases lt_trichotomy p.2 p.1 with hlt | heq | hgt
  · simp [Set.indicator, hlt, hpB hlt]
  · exact False.elim (hpdiag heq.symm)
  · have hnot : ¬ p.2 < p.1 := not_lt_of_ge hgt.le
    simp [Set.indicator, hnot, hpS hgt]

theorem Q_ae (D : MSData) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc D.a1 D.b1)),
      D.Q t = D.nu.real {c | c < t} := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  have hsections : ∀ᵐ t ∂D.mu,
      (fun c => D.q (t, c)) =ᵐ[D.nu]
        (fun c => Set.indicator {p : ℝ × ℝ | p.2 < p.1} 1 (t, c)) := by
    filter_upwards [Measure.ae_ae_eq_curry_of_prod D.q_ae_ind] with t ht
    filter_upwards [ht] with c hc
    exact hc
  have hQ : ∀ᵐ t ∂D.mu, D.Q t = D.nu.real {c | c < t} := by
    filter_upwards [hsections] with t ht
    rw [Q_def, interimQ]
    calc
      (∫ c, D.q (t, c) ∂D.nu) =
          ∫ c, Set.indicator {p : ℝ × ℝ | p.2 < p.1} 1 (t, c) ∂D.nu :=
        integral_congr_ae ht
      _ = ∫ c, (Set.Iio t).indicator (fun _ => (1 : ℝ)) c ∂D.nu := by
        rfl
      _ = D.nu.real {c | c < t} := by
        rw [integral_indicator_const (1 : ℝ) measurableSet_Iio]
        simp [smul_eq_mul, Set.Iio]
  exact D.vol_absB.ae_le hQ

theorem R_ae (D : MSData) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc D.a2 D.b2)),
      D.R t = D.mu.real {v | t < v} := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  have hsections : ∀ᵐ t ∂D.nu,
      (fun v => D.q (v, t)) =ᵐ[D.mu]
        (fun v => Set.indicator {p : ℝ × ℝ | p.2 < p.1} 1 (v, t)) := by
    have hmap : (D.nu.prod D.mu).map Prod.swap = D.mu.prod D.nu := by
      rw [Measure.prod_swap]
    have h₀ : D.q =ᵐ[(D.nu.prod D.mu).map Prod.swap]
        (fun p => Set.indicator {p : ℝ × ℝ | p.2 < p.1} 1 p) := by
      rw [hmap]
      exact D.q_ae_ind
    have hs := ae_eq_comp measurable_swap.aemeasurable h₀
    filter_upwards [Measure.ae_ae_eq_curry_of_prod hs] with t ht
    filter_upwards [ht] with v hv
    exact hv
  have hR : ∀ᵐ t ∂D.nu, D.R t = D.mu.real {v | t < v} := by
    filter_upwards [hsections] with t ht
    rw [R_def, interimR]
    calc
      (∫ v, D.q (v, t) ∂D.mu) =
          ∫ v, Set.indicator {p : ℝ × ℝ | p.2 < p.1} 1 (v, t) ∂D.mu :=
        integral_congr_ae ht
      _ = ∫ v, (Set.Ioi t).indicator (fun _ => (1 : ℝ)) v ∂D.mu := by
        rfl
      _ = D.mu.real {v | t < v} := by
        rw [integral_indicator_const (1 : ℝ) measurableSet_Ioi]
        simp [smul_eq_mul, Set.Ioi]
  exact D.vol_absS.ae_le hR

noncomputable def S (D : MSData) : ℝ :=
  ∫ p, max (p.1 - p.2) 0 ∂(D.mu.prod D.nu)

/-- The measure of profiles with a cost below `t` and a value above `t`. -/
noncomputable def H (D : MSData) (t : ℝ) : ℝ :=
  D.nu.real {c | c < t} * D.mu.real {v | t < v}

theorem H_nonneg (D : MSData) (t : ℝ) : 0 ≤ D.H t := by
  exact mul_nonneg measureReal_nonneg measureReal_nonneg

theorem H_meas (D : MSData) : Measurable D.H := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  have hν : Monotone (fun t : ℝ => D.nu.real {c | c < t}) := by
    intro t u htu
    exact measureReal_mono (fun c hc => lt_of_lt_of_le hc htu) (by finiteness)
  have hμ : Antitone (fun t : ℝ => D.mu.real {v | t < v}) := by
    intro t u htu
    exact measureReal_mono (fun v hv => lt_of_le_of_lt htu hv) (by finiteness)
  exact hν.measurable.mul hμ.measurable

theorem H_eq_zero_left (D : MSData) {t : ℝ} (ht : t ≤ D.a2) : D.H t = 0 := by
  have hν : D.nu {c | c < t} = 0 := by
    apply measure_mono_null
      (s := {c | c < t}) (t := D.nu.supportᶜ)
    · intro c hc hcs
      have hca := (D.nu_supported hcs).1
      exact (not_lt_of_ge (le_trans ht hca)) hc
    · exact Measure.measure_compl_support
  simp [H, Measure.real, hν]

theorem H_eq_zero_right (D : MSData) {t : ℝ} (ht : D.b1 ≤ t) : D.H t = 0 := by
  have hμ : D.mu {v | t < v} = 0 := by
    apply measure_mono_null
      (s := {v | t < v}) (t := D.mu.supportᶜ)
    · intro v hv hvs
      have hvb := (D.mu_supported hvs).2
      exact (not_lt_of_ge (le_trans hvb ht)) hv
    · exact Measure.measure_compl_support
  simp [H, Measure.real, hμ]

theorem B_eq (D : MSData) :
    (∫ t in D.a1..D.b1, D.Q t * D.mu.real {v | t ≤ v}) =
      ∫ t in D.a1..D.b1, D.H t := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  letI : NullSingletonClass D.mu := D.mu_noAtoms
  have hQ : ∀ᵐ t ∂(volume.restrict (Set.uIoc D.a1 D.b1)),
      D.Q t = D.nu.real {c | c < t} := by
    apply ae_restrict_of_ae_restrict_of_subset
      (s := Set.uIoc D.a1 D.b1) (t := Set.Icc D.a1 D.b1) ?_ D.Q_ae
    rw [Set.uIoc_of_le D.h1.le]
    exact Set.Ioc_subset_Icc_self
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hQ] with t ht
  have hμ : D.mu.real {v | t ≤ v} = D.mu.real {v | t < v} := by
    apply measureReal_congr
    filter_upwards [Measure.ae_ne D.mu t] with v hv
    apply propext
    constructor
    · intro h
      exact lt_of_le_of_ne h (Ne.symm hv)
    · exact le_of_lt
  rw [ht, hμ]
  rfl

theorem C_eq (D : MSData) :
    (∫ t in D.a2..D.b2, D.R t * D.nu.real {c | c ≤ t}) =
      ∫ t in D.a2..D.b2, D.H t := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  letI : NullSingletonClass D.nu := D.nu_noAtoms
  have hR : ∀ᵐ t ∂(volume.restrict (Set.uIoc D.a2 D.b2)),
      D.R t = D.mu.real {v | t < v} := by
    apply ae_restrict_of_ae_restrict_of_subset
      (s := Set.uIoc D.a2 D.b2) (t := Set.Icc D.a2 D.b2) ?_ D.R_ae
    rw [Set.uIoc_of_le D.h2.le]
    exact Set.Ioc_subset_Icc_self
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hR] with t ht
  have hν : D.nu.real {c | c ≤ t} = D.nu.real {c | c < t} := by
    apply measureReal_congr
    filter_upwards [Measure.ae_ne D.nu t] with c hc
    apply propext
    constructor
    · intro h
      exact lt_of_le_of_ne h hc
    · exact le_of_lt
  rw [ht, hν]
  dsimp [H]
  ring

theorem S_layercake (D : MSData) :
    D.S = ∫ t in D.a2..D.b1, D.H t := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  letI : IsFiniteMeasure (volume.restrict (Set.uIoc D.a2 D.b1)) := by
    apply MeasureTheory.isFiniteMeasure_restrict.mpr
    rw [Set.uIoc_of_le D.h3.le]
    exact measure_Ioc_lt_top.ne
  let F : ℝ → ℝ × ℝ → ℝ := fun t p =>
    {z : ℝ × (ℝ × ℝ) | z.2.2 < z.1 ∧ z.1 < z.2.1}.indicator
      (fun _ => (1 : ℝ)) (t, p)
  have hA : MeasurableSet
      {z : ℝ × (ℝ × ℝ) | z.2.2 < z.1 ∧ z.1 < z.2.1} := by
    exact (measurableSet_lt (measurable_snd.comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst (measurable_fst.comp measurable_snd))
  have hFmeas : Measurable (Function.uncurry F) := by
    change Measurable
      ({z : ℝ × (ℝ × ℝ) | z.2.2 < z.1 ∧ z.1 < z.2.1}.indicator
        (fun _ => (1 : ℝ)))
    exact measurable_const.indicator hA
  have hFint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc D.a2 D.b1)).prod (D.mu.prod D.nu)) := by
    apply Integrable.of_bound hFmeas.aestronglyMeasurable 1
    filter_upwards with z
    change ‖({z : ℝ × (ℝ × ℝ) | z.2.2 < z.1 ∧ z.1 < z.2.1}.indicator
      (fun _ => (1 : ℝ)) z)‖ ≤ 1
    by_cases hz : z.2.2 < z.1 ∧ z.1 < z.2.1 <;> simp [hz]
  have hμsupp : ∀ᵐ v ∂D.mu, v ∈ D.mu.support := by
    rw [ae_iff]
    change D.mu D.mu.supportᶜ = 0
    exact Measure.measure_compl_support
  have hνsupp : ∀ᵐ c ∂D.nu, c ∈ D.nu.support := by
    rw [ae_iff]
    change D.nu D.nu.supportᶜ = 0
    exact Measure.measure_compl_support
  have hμprod : ∀ᵐ p ∂(D.mu.prod D.nu), p.1 ∈ D.mu.support := by
    rw [Measure.ae_prod_iff_ae_ae
      (show MeasurableSet {p : ℝ × ℝ | p.1 ∈ D.mu.support} from
        measurableSet_preimage measurable_fst Measure.isClosed_support.measurableSet)]
    filter_upwards [hμsupp] with v hv
    exact Filter.Eventually.of_forall fun _ => hv
  have hνprod : ∀ᵐ p ∂(D.mu.prod D.nu), p.2 ∈ D.nu.support := by
    rw [Measure.ae_prod_iff_ae_ae
      (show MeasurableSet {p : ℝ × ℝ | p.2 ∈ D.nu.support} from
        measurableSet_preimage measurable_snd Measure.isClosed_support.measurableSet)]
    filter_upwards with v
    filter_upwards [hνsupp] with c hc
    exact hc
  have htypes : ∀ᵐ p ∂(D.mu.prod D.nu),
      p.1 ∈ Set.Icc D.a1 D.b1 ∧ p.2 ∈ Set.Icc D.a2 D.b2 := by
    filter_upwards [hμprod, hνprod] with p hpv hpc
    exact ⟨D.mu_supported hpv, D.nu_supported hpc⟩
  have hpointwise (p : ℝ × ℝ)
      (hp : p.1 ∈ Set.Icc D.a1 D.b1 ∧ p.2 ∈ Set.Icc D.a2 D.b2) :
      max (p.1 - p.2) 0 = ∫ t in D.a2..D.b1, F t p := by
    let A : Set ℝ := {t | p.2 < t ∧ t < p.1}
    have hAmeas : MeasurableSet A := by
      change MeasurableSet (Set.Ioo p.2 p.1)
      exact measurableSet_Ioo
    have hAsub : A ⊆ Set.Ioc D.a2 D.b1 := by
      intro t ht
      exact ⟨lt_of_le_of_lt hp.2.1 ht.1, le_of_lt (ht.2.trans_le hp.1.2)⟩
    have hvol : volume.real A = max (p.1 - p.2) 0 := by
      change volume.real (Set.Ioo p.2 p.1) = _
      rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal']
    rw [intervalIntegral.integral_of_le D.h3.le]
    change max (p.1 - p.2) 0 =
      ∫ t in Set.Ioc D.a2 D.b1, A.indicator (fun _ => (1 : ℝ)) t ∂volume
    rw [setIntegral_indicator hAmeas, Set.inter_eq_right.mpr hAsub,
      setIntegral_const]
    simpa [smul_eq_mul, mul_one] using hvol.symm
  have hinner (t : ℝ) :
      (∫ p, F t p ∂(D.mu.prod D.nu)) = D.H t := by
    have hfun : (fun p : ℝ × ℝ => F t p) = fun p =>
        (Set.Ioi t).indicator (fun _ => (1 : ℝ)) p.1 *
          (Set.Iio t).indicator (fun _ => (1 : ℝ)) p.2 := by
      funext p
      by_cases hpv : t < p.1 <;> by_cases hpc : p.2 < t <;>
        simp [F, hpv, hpc]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun p => congrFun hfun p),
      integral_prod_mul]
    rw [integral_indicator_const 1 measurableSet_Ioi,
      integral_indicator_const 1 measurableSet_Iio]
    simp [H, Set.Ioi, Set.Iio, smul_eq_mul, mul_comm]
  calc
    D.S = ∫ p, ∫ t in D.a2..D.b1, F t p ∂volume ∂(D.mu.prod D.nu) := by
      unfold S
      apply integral_congr_ae
      filter_upwards [htypes] with p hp
      exact hpointwise p hp
    _ = ∫ t in D.a2..D.b1, ∫ p, F t p ∂(D.mu.prod D.nu) ∂volume :=
      (intervalIntegral_integral_swap hFint).symm
    _ = ∫ t in D.a2..D.b1, D.H t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t _
      exact hinner t

theorem eff_payoff (D : MSData) :
    (∫ p, (p.1 - p.2) * D.q p ∂(D.mu.prod D.nu)) = D.S := by
  unfold S
  apply integral_congr_ae
  have hdiag : ∀ᵐ p ∂(D.mu.prod D.nu), p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa [not_ne_iff] using D.diag_null
  filter_upwards [D.q_ae_ind, hdiag] with p hq hpdiag
  rcases lt_trichotomy p.2 p.1 with hlt | heq | hgt
  · rw [hq]
    simp [Set.indicator, hlt, max_eq_left (sub_nonneg.mpr hlt.le)]
  · exact False.elim (hpdiag heq.symm)
  · rw [hq]
    have hnot : ¬ p.2 < p.1 := not_lt_of_ge hgt.le
    simp [Set.indicator, hnot, max_eq_right (sub_nonpos.mpr hgt.le)]

theorem H_pos (D : MSData) :
    ∀ t ∈ Set.Ioo (max D.a1 D.a2) (min D.b1 D.b2), 0 < D.H t := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  intro t ht
  have ha2t : D.a2 < t := lt_of_le_of_lt (le_max_right D.a1 D.a2) ht.1
  have htb1 : t < D.b1 := lt_of_lt_of_le ht.2 (min_le_left D.b1 D.b2)
  have hνpos : 0 < D.nu.real {c | c < t} := by
    have hleft : D.a2 < min t D.b2 := lt_min ha2t D.h2
    obtain ⟨c, hc⟩ := Set.nonempty_Ioo.mpr hleft
    have hcSupport : c ∈ Set.Ioo D.a2 D.b2 :=
      ⟨hc.1, lt_of_lt_of_le hc.2 (min_le_right t D.b2)⟩
    have hmeasure := D.nu_fullSupport (Set.Ioo D.a2 (min t D.b2)) isOpen_Ioo
      ⟨c, hc, hcSupport⟩
    have hsubset : Set.Ioo D.a2 (min t D.b2) ⊆ {c | c < t} := by
      intro c hc
      exact hc.2.trans_le (min_le_left t D.b2)
    have hraw : 0 < D.nu {c | c < t} := lt_of_lt_of_le hmeasure (measure_mono hsubset)
    exact ENNReal.toReal_pos hraw.ne' (by finiteness)
  have hμpos : 0 < D.mu.real {v | t < v} := by
    have hright : max t D.a1 < D.b1 := max_lt htb1 D.h1
    obtain ⟨v, hv⟩ := Set.nonempty_Ioo.mpr hright
    have hvSupport : v ∈ Set.Ioo D.a1 D.b1 :=
      ⟨lt_of_le_of_lt (le_max_right t D.a1) hv.1, hv.2⟩
    have hmeasure := D.mu_fullSupport (Set.Ioo (max t D.a1) D.b1) isOpen_Ioo
      ⟨v, hv, hvSupport⟩
    have hsubset : Set.Ioo (max t D.a1) D.b1 ⊆ {v | t < v} := by
      intro v hv
      exact lt_of_le_of_lt (le_max_left t D.a1) hv.1
    have hraw : 0 < D.mu {v | t < v} := lt_of_lt_of_le hmeasure (measure_mono hsubset)
    exact ENNReal.toReal_pos hraw.ne' (by finiteness)
  exact mul_pos hνpos hμpos

theorem BC_gt_S (D : MSData) :
    (∫ t in D.a1..D.b1, D.Q t * D.mu.real {v | t ≤ v}) +
      (∫ t in D.a2..D.b2, D.R t * D.nu.real {c | c ≤ t}) > D.S := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  let l := max D.a1 D.a2
  let r := min D.b1 D.b2
  have hlr : l < r := by
    dsimp [l, r]
    exact lt_min (max_lt_iff.mpr ⟨D.h1, D.h3⟩)
      (max_lt_iff.mpr ⟨D.h4, D.h2⟩)
  have hHle (t : ℝ) : D.H t ≤ 1 := by
    have hν : D.nu.real {c | c < t} ≤ 1 := by
      calc
        D.nu.real {c | c < t} ≤ D.nu.real Set.univ :=
          measureReal_mono (Set.subset_univ _) (by finiteness)
        _ = 1 := by simp
    have hμ : D.mu.real {v | t < v} ≤ 1 := by
      calc
        D.mu.real {v | t < v} ≤ D.mu.real Set.univ :=
          measureReal_mono (Set.subset_univ _) (by finiteness)
        _ = 1 := by simp
    change D.nu.real {c | c < t} * D.mu.real {v | t < v} ≤ 1
    calc
      D.nu.real {c | c < t} * D.mu.real {v | t < v} ≤
          1 * D.mu.real {v | t < v} :=
        mul_le_mul_of_nonneg_right hν measureReal_nonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hμ (by norm_num)
      _ = 1 := by norm_num
  have hInterval (a b : ℝ) : IntervalIntegrable D.H volume a b := by
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound ?_ D.H_meas.aestronglyMeasurable 1 ?_
    · rcases le_total a b with hab | hba
      · rw [Set.uIoc_of_le hab]
        exact measure_Ioc_lt_top
      · rw [Set.uIoc_of_ge hba]
        exact measure_Ioc_lt_top
    · filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (D.H_nonneg t)]
      exact hHle t
  have hBzero : (∫ t in D.a1..l, D.H t) = 0 := by
    by_cases ha : D.a1 ≤ D.a2
    · have heq : l = D.a2 := max_eq_right ha
      rw [heq]
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      exact D.H_eq_zero_left (le_trans ht.2 (le_of_eq heq))
    · have ha' : D.a2 ≤ D.a1 := le_of_not_ge ha
      simp [l, max_eq_left ha']
  have hBshort :
      (∫ t in D.a1..D.b1, D.H t) = ∫ t in l..D.b1, D.H t := by
    calc
      (∫ t in D.a1..D.b1, D.H t) =
          (∫ t in D.a1..l, D.H t) + ∫ t in l..D.b1, D.H t :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hInterval D.a1 l) (hInterval l D.b1)).symm
      _ = ∫ t in l..D.b1, D.H t := by rw [hBzero]; simp
  have hCzero : (∫ t in r..D.b2, D.H t) = 0 := by
    by_cases hb : D.b1 ≤ D.b2
    · have heq : r = D.b1 := min_eq_left hb
      rw [heq]
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      have hbt : D.b1 < t := by
        rw [← heq]
        exact ht.1
      exact D.H_eq_zero_right hbt.le
    · have hb' : D.b2 ≤ D.b1 := le_of_not_ge hb
      simp [r, min_eq_right hb']
  have hCshort :
      (∫ t in D.a2..D.b2, D.H t) = ∫ t in D.a2..r, D.H t := by
    calc
      (∫ t in D.a2..D.b2, D.H t) =
          (∫ t in D.a2..r, D.H t) + ∫ t in r..D.b2, D.H t :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hInterval D.a2 r) (hInterval r D.b2)).symm
      _ = ∫ t in D.a2..r, D.H t := by rw [hCzero]; simp
  have hadd1 :
      (∫ t in D.a2..l, D.H t) + ∫ t in l..r, D.H t =
        ∫ t in D.a2..r, D.H t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hInterval D.a2 l) (hInterval l r)
  have hadd2 :
      (∫ t in D.a2..l, D.H t) + ∫ t in l..D.b1, D.H t =
        ∫ t in D.a2..D.b1, D.H t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hInterval D.a2 l) (hInterval l D.b1)
  have hpositive : 0 < ∫ t in l..r, D.H t := by
    have hIntervalPos := hInterval l r
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc l r)] D.H :=
      ae_of_all _ fun t => D.H_nonneg t
    have hIntegrableOn : IntegrableOn D.H (Set.Ioc l r) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hlr.le).mp hIntervalPos
    rw [intervalIntegral.integral_of_le hlr.le]
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hIntegrableOn).2
    have hsubset : Set.Ioo l r ⊆ Function.support D.H ∩ Set.Ioc l r := by
      intro t ht
      constructor
      · change D.H t ≠ 0
        exact (D.H_pos t ht).ne'
      · exact ⟨ht.1, ht.2.le⟩
    have hvol : 0 < volume (Set.Ioo l r) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlr)
    exact lt_of_lt_of_le hvol (measure_mono hsubset)
  rw [B_eq, C_eq, S_layercake, hBshort, hCshort]
  have hdiff :
      ((∫ t in l..D.b1, D.H t) + (∫ t in D.a2..r, D.H t)) -
        (∫ t in D.a2..D.b1, D.H t) = ∫ t in l..r, D.H t := by
    let x : ℝ := ∫ t in D.a2..l, D.H t
    let y : ℝ := ∫ t in l..r, D.H t
    let z : ℝ := ∫ t in l..D.b1, D.H t
    let u : ℝ := ∫ t in D.a2..r, D.H t
    let v : ℝ := ∫ t in D.a2..D.b1, D.H t
    have h1 : x + y = u := by
      change (∫ t in D.a2..l, D.H t) + ∫ t in l..r, D.H t =
        ∫ t in D.a2..r, D.H t
      exact hadd1
    have h2 : x + z = v := by
      change (∫ t in D.a2..l, D.H t) + ∫ t in l..D.b1, D.H t =
        ∫ t in D.a2..D.b1, D.H t
      exact hadd2
    change (z + u) - v = y
    calc
      (z + u) - v = (z + (x + y)) - v :=
        congrArg (fun w : ℝ => (z + w) - v) h1.symm
      _ = (z + (x + y)) - (x + z) :=
        congrArg (fun w : ℝ => (z + (x + y)) - w) h2.symm
      _ = y := by ring
  apply sub_pos.mp
  calc
    0 < ∫ t in l..r, D.H t := hpositive
    _ = ((∫ t in l..D.b1, D.H t) + (∫ t in D.a2..r, D.H t)) -
        (∫ t in D.a2..D.b1, D.H t) := hdiff.symm

end MSData
