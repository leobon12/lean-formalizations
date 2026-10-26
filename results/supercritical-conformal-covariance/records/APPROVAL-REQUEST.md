# Public extract of the revision 2.2 statement approval request

Every frozen file's module comment cites the development file `planning/candidates/rev2.2/APPROVAL-REQUEST.md` and the
candidate file whose declaration it froze. This is the public, release-specific extract of that request, not a byte-for-byte copy. The original
request has SHA-256 `cbc72606a87f4769f9817cdf20299db937ccb151aab528a91145413e43c32bfe` (development commit `bb67bbe3c`). Ruling A15 records the
author's delegated approval; see [the rulings excerpt](RULINGS-EXCERPT.md). The exact theorem heads and the meaning-carrying definitions are in
the result guide and in the frozen Lean files, which ship byte-identical to the sealed development commit.

## The candidate files

Each frozen file says that its declaration is unchanged from an approved candidate file. The candidates were transient files elaborated during
the statement review; the request lists them with these SHA-256 values. Each frozen comment prints the first 16 hexadecimal digits.

| Frozen declaration | Candidate file | Candidate SHA-256 |
| --- | --- | --- |
| `conformal_covariance` | `CandConformalCovariance.lean` | `b482f49bd8897ca6605f7d527877005dd40e883d027d54dfd67b414829d1e291` |
| `domainMetric_ae_eq_of_isDomainRealization` | `CandDomainMetricAeEq.lean` | `a967423a6555c96560f998e4349f4311d907e0e0f7975602ff44b2d3c522e7ed` |
| `IsConformalBijection` | `CandIsConformalBijection.lean` | `c1433aa54740d034335a8b832f056d909f4a25516fb1eb90eb8c63a004da5ced` |
| `confPushTest` | `CandConfPushTest.lean` | `5462cdc4ba63111fd83d15119e841b2a9ca3f9e92f983a86c02bb1dd03f6d533` |
| `confPullbackField` | `CandConfPullbackField.lean` | `6fe3dc08cc3c9dfe46b14ca55ffc5a6cf107b9ec380af9ba9a6ee89810409bb4` |
| `IsDomainRealization` | `CandIsDomainRealization.lean` | `493cc38523c6f597d9b8dc8557e1167e4aa6cb95c63549f5b2a6f968bcf7a726` |
| `weylScaleOn` | `CandWeylScaleOn.lean` | `10eb1c0dcdbe6cf49a361ac55f11e5fcfdef7f928acb60bb7d7566d57639c10d` |
| `domainMetric` | `CandDomainMetric.lean` | `6ae042c464c3f3705c5e473a155265a3427e3e76b4ff557eb834b4c80e95b98f` |
| `xiCrit` | `CandXiCrit.lean` | `a7d5394767b41a9d612906500abad631b4b33b64aa5b8e1fb2bec475c641a6e6` |
| `IsGreenian` | `CandIsGreenian.lean` | `40b18d172a6875e3210d5e4a65f86088b95b95033be3f047489f6e6b00b1ded6` |

## The six disclosures (request §4)

1. U and V are **Greenian** domains, so that the zero-boundary GFF exists. This is ruling A14; the printed theorem says only “domains”.
2. The field class is a **global realization** `h = h₀|_V + f`. A locally defined GFF plus continuous function need not have one global
   representation. The request gave the punctured-disk composition with `z ↦ z²` as the counterexample.
3. “One fixed normalization” is represented by **every strong LQG metric D**, using the strong uniqueness theorem and homogeneity.
4. The `ξ > ξ_crit` premise is transcribed literally. Its infimum convention may strengthen the Lean result; the proof uses `Q > 0` instead,
   leaving that premise idle.
5. `confPushTest` and `IsGreenian` **inline two library definitions**, respectively the test-function transport and zero-boundary
   admissibility, to freeze their mathematical meanings.
6. The root has a genuine **existence conjunct** constructing a realization of the pulled-back field on a measure-preserving extension. The
   universal metric equality cannot be satisfied vacuously through an empty class of realizations.

The private request also recorded proof progress at the time of approval; that is omitted here. The current proof status is in the guide.
