# frozen_string_literal: true

# 中核（crates/fmspec-core）の Verus による検証（仕様書 §14.1、§14.3）。
#
# `rake verus` は、証明を通すだけでなく、証明が空虚でないことも検査する。
#
# - verus:trusted   信頼する項目（assume、admit、external_body など）が1つもない。
# - verus:contract  未検証コードから呼べる公開関数が、前提条件（requires）を持たない（仕様書 §3.1）。
# - verus:mutants   検査を1つ壊した変異と、到達点に assert(false) を置いた変種が、証明に失敗する。
#
# Verus の実行ファイルは環境変数 VERUS で指定する（なければ PATH の verus）。
# バージョンは VERUS_VERSION に固定する。更新は証明の再確認とあわせて行う。
require "open3"
require "tmpdir"
require "fileutils"

VERUS_VERSION = "0.2026.10.04.426d8b0"
VERUS_CRATE = File.join(ROOT, "crates/fmspec-core")
VERUS_SOURCES = Dir[File.join(VERUS_CRATE, "src/*.rs")].sort
# 証明の対象外の、標準トレイトの手書き実装。`verus!` の外にあり、判定の経路から呼ばれない。
VERUS_UNVERIFIED = %w[impls.rs].freeze

VERUS_TRUST = /#\[verifier::external(?:_body|_fn_specification|_type_specification)?\]|\bassume_specification\b|\bassume\(|\badmit\(\s*\)|exec_allows_no_decreases_clause|#\[verifier::truncate\]/

def verus_bin
  ENV.fetch("VERUS", "verus")
end

def verus_code(path)
  File.read(path).gsub(%r{/\*.*?\*/}m, "").lines.map { |l| l.sub(%r{//.*$}, "") }.join
end

# Verus を実行し、[成功したか, 検証した数, エラーの数, 出力] を返す。エラーの数が nil なら、検証まで進んでいない。
def verus_run(dir)
  out, status = Open3.capture2e(verus_bin, "--crate-type=lib", File.join(dir, "src/lib.rs"))
  m = out.match(/verification results:: (\d+) verified, (\d+) errors/)
  [status.success?, m && m[1].to_i, m && m[2].to_i, out]
end

# 変異。[ファイル, 元の文字列, 置き換え, 説明]。元の文字列はファイルにちょうど1回現れなければならない。
VERUS_MUTANTS = [
  ["keys.rs", "p[i / d.len() as int].push(d[i % d.len() as int])", "p[i % p.len() as int].push(d[i / p.len() as int])",
   "Tupleの正規順で最初の要素を最も速く変える"],
  ["keys.rs", "seq![SVal::None] + domain(*x, enums).map_values(|v: SVal| SVal::Some(Box::new(v))),",
   "domain(*x, enums).map_values(|v: SVal| SVal::Some(Box::new(v))) + seq![SVal::None],", "Optionの空を最後に並べる"],
  ["keys.rs", "(SType::Int(lo, _), SVal::Int(x)) => x - lo,", "(SType::Int(lo, _), SVal::Int(x)) => x as int,", "整数の番号から下端を引かない"],
  ["encoding.rs", "        SType::Option(x) => 1 + width(*x, enums),", "        SType::Option(x) => width(*x, enums),",
   "Optionの幅に有無のスロットを数えない"],
  ["encoding.rs", "SVal::List(items) => seq![Value::Int(items.len() as i64)] + enc_items(", "SVal::List(items) => enc_items(",
   "Listの符号化に長さを入れない"],
  ["encoding.rs", "        SType::Enum(id) => id < enums.len() && enums[id as int] >= 1,",
   "        SType::Enum(id) => id < enums.len() && enums[id as int] >= 0,", "ラベルのない列挙型を整形式とする"],
  ["map_encoding.rs", "let tag: i64 = if present { 1 } else { 0 };",
   "let tag: i64 = if present { 0 } else { 1 };", "Mapの符号化でキーの有無を反転する"],
  ["ranking.rs", "prefix.checked_mul(radix)?.checked_add(digit)",
   "prefix.checked_mul(radix)?.checked_add(0)", "キー値を符号化する順位計算で末尾の成分を落とす"],
  ["bindings.rs", "out = Expr::Let(Box::new(binding), Box::new(out));",
   "out = Expr::Let(Box::new(out), Box::new(binding));", "束縛より先に本体を評価する"],
  ["map_lookup.rs", "let offset = base + column;", "let offset = base;", "Mapの値列でも有無フラグを読む"],
  ["ranking.rs", "let base = Expr::Bin(BinOp::Mul,", "let base = Expr::Bin(BinOp::Add,",
   "複合キーの順位で基数を掛けずに足す"],
  ["map_lookup.rs", "            BinOp::Lt,", "            BinOp::Ge,",
   "Mapの値を選ぶときに二分木の枝を逆にする"],
  ["map_lookup.rs", "Box::new(Expr::Fail(Type::Bool, MISSING_KEY)),", "Box::new(Expr::Const(Value::Bool(true))),",
   "Mapの欠損キーで失敗しない"],
  ["eval.rs", "BinOp::Add => checked(a.checked_add(*b)),", "BinOp::Add => checked(a.checked_sub(*b)),",
   "加算を減算として実行する"],
  ["eval.rs", "BinOp::Mul => checked(a.checked_mul(*b)),", "BinOp::Mul => Ok(Value::Int(a.wrapping_mul(*b))),",
   "乗算のオーバーフローを循環させる"],
  ["eval.rs", "            Ok(false) => Ok(Value::Bool(true)),\n            Ok(true) => match to_bool(eval_in(b, c, ls)) {",
   "            Ok(false) => Ok(Value::Bool(false)),\n            Ok(true) => match to_bool(eval_in(b, c, ls)) {",
   "implies の前件が偽のときに偽を返す"],
  ["eval.rs", "        Expr::And(a, b) => match to_bool(eval_in(a, c, ls)) {\n            Err(k) => Err(k),\n            Ok(false) => Ok(Value::Bool(false)),",
   "        Expr::And(a, b) => match to_bool(eval_in(a, c, ls)) {\n            Err(k) => Err(k),\n            Ok(false) => to_bool(eval_in(b, c, ls)).map(|_| Value::Bool(false)),",
   "all の短絡評価をやめる"],
  ["eval.rs", "                    int_result_exec(floor_divmod(*a, *b).0)", "                    int_result_exec(floor_divmod(*a, *b).1)",
   "除算で余りを返す"],
  ["eval.rs", "        (-(t as i128) - 1, d - (r0 as i128) - 1)", "        (-(t as i128), d - (r0 as i128) - 1)",
   "負の数の除算を0の方向に丸める"],
  ["eval.rs", "                BinOp::Mod => if *b == 0 {\n                    Err(ErrKind::DivByZero)",
   "                BinOp::Mod => if *b == 0 && *a == 0 {\n                    Err(ErrKind::DivByZero)", "0による剰余を一部しか検査しない"],
  ["eval.rs", "                inner.push(v);\n                eval_in(b, c, &inner)", "                eval_in(b, c, ls)",
   "let で値を束縛しない"],
  ["eval.rs", "            Ok(ls[*i])", "            Ok(ls[ls.len() - 1])", "局所変数を常に最も内側の束縛として読む"],
  ["eval.rs", "    while x <= hi as i128\n", "    while x < hi as i128\n", "量化の範囲の最後の値をたどらない"],
  ["eval.rs", "                if b != all {\n                    return Ok(Value::Bool(b));", "                if b != all && x > lo as i128 {\n                    return Ok(Value::Bool(b));",
   "量化の最初の値で打ち切らない"],
  ["eval.rs", "    Ok(Value::Bool(all))\n}", "    Ok(Value::Bool(true))\n}", "空の exists を真とする"],
  ["eval.rs", "        Value::Enum(_, k) => *k,", "        Value::Enum(id, _) => *id as i64,", "列挙型の符号に型の添字を返す"],
  ["step.rs", "        (Type::Int(lo, hi), Value::Int(x)) => if *lo <= *x && *x <= *hi {",
   "        (Type::Int(lo, hi), Value::Int(x)) => if *lo <= *x {", "範囲外更新の上限を検査しない"],
  ["step.rs", "                                    t.set(u.target, x);", "", "状態更新を適用しない"],
  ["step.rs", "        Ok(false) => StepR::Disabled,\n        Ok(true) => {", "        Ok(_) => {",
   "guard が偽でも遷移する"],
  ["step.rs", "    while v <= hi\n", "    while v < hi\n", "引数のドメインの最後の値を列挙しない"],
  ["step.rs", "                ts.push(tr);", "", "有効な遷移を列挙から落とす"],
  ["step.rs", "            StepR::Fail(site, k) => {\n                return Some((copy_vec(prefix), site, k));\n            },",
   "            StepR::Fail(site, k) => {},", "評価エラーの遷移を黙って除外する"],
  ["typing.rs", "                return Err(InvalidModel::DuplicateUpdate(a, u));", "", "重複代入を拒否しない"],
  ["typing.rs", "            (Some(ETy::Bool), Some(x), Some(y)) => if ety_eq(&x, &y) {\n                Some(x)\n            } else {\n                None\n            },\n            _ => None,\n        },\n        Expr::Local(i) => if *i < lt.len() {",
   "            (Some(ETy::Bool), Some(x), Some(y)) => Some(x),\n            _ => None,\n        },\n        Expr::Local(i) => if *i < lt.len() {",
   "ite の枝の型の一致を検査しない"],
  ["typing.rs", "        Expr::Forall(ty, lo, hi, body) => if quant_dom_ok_exec(t.enums, ty, *lo, *hi) && is_bool(",
   "        Expr::Forall(ty, lo, hi, body) => if is_bool(", "量化の範囲が型に収まることを検査しない"],
  ["typing.rs", "            Some(x) => type_in(b, t, &with_ety(lt, x)),", "            Some(x) => type_in(b, t, lt),",
   "let の本体の型検査で束縛した変数を数えない"],
  ["typing.rs", "        if !vals_ok_exec(&m.enums, &m.state_types, &m.inits[i]) {\n            return Err(InvalidModel::Initial(i));\n        }\n", "",
   "初期状態の型を検査しない"],
  ["typing.rs", "    if m.inits.len() == 0 {\n        return Err(InvalidModel::NoInitial);\n    }\n", "", "初期状態がないモデルを受理する"],
  ["cert.rs", "        if !find(cert, &m.inits[i]) {\n            return Some(Reject::MissingInitial(i));\n        }\n", "",
   "証明書に初期状態があることを検査しない"],
  ["cert.rs", "    while i < m.inits.len()\n        invariant\n            i <= m.inits@.len(),\n            forall|j: int| 0 <= j < i ==> in_cert",
   "    while i < m.inits.len() && i < 1\n        invariant\n            i <= m.inits@.len(),\n            forall|j: int| 0 <= j < i ==> in_cert",
   "証明書の検査で2番目以降の初期状態を調べない"],
  ["cert.rs", "                if !find(cert, &t.state) {\n                    return Err(Reject::MissingSuccessor(k, a));\n                }\n", "",
   "遷移先が証明書にあることを検査しない"],
  ["cert.rs", "                        return Err(Reject::ContractNotHeld(k, con));", "", "証明書の検査で遷移契約を無視する"],
  ["cert.rs", "            return Some(Reject::InvariantNotHeld(k, i));", "", "証明書の検査で不変条件を無視する"],
  ["cert.rs", "                return Some(Reject::Deadlock(k));", "", "証明書の検査でデッドロックを無視する"],
  ["cert.rs", "        Enumerated::Fail(_, _, _) => Err(Reject::StepFailed(k, a)),", "        Enumerated::Fail(_, _, _) => Ok(false),",
   "証明書の検査で評価エラーを無視する"],
  ["cert.rs", "        if c == 0 {\n            assert(cert@[mid as int]@ == t@);", "        if c <= 0 {\n            assert(cert@[mid as int]@ == t@);",
   "等しくない状態を証明書の要素とみなす"],
  ["cert.rs", "        if act_on_exec(m, c, a) {\n            match check_action(m, c, cert, k, a, s) {",
   "        if act_on_exec(m, c, a) && a > 0 {\n            match check_action(m, c, cert, k, a, s) {",
   "証明書の検査で最初の操作を調べない"],
  ["trace.rs", "    if !is_initial(m, start) {\n        return Some(Reject::BadStart);\n    }\n", "", "トレースの開始状態が初期状態であることを検査しない"],
  ["trace.rs", "        if vec_eq(&m.inits[i], s) {", "        if vec_eq(&m.inits[0], s) || i > 0 {", "初期状態でない開始状態を受理する"],
  ["trace.rs", "                if !vec_eq(&t, &st.state) || !opt_eq(&o, &st.output) {", "                if !opt_eq(&o, &st.output) {",
   "トレースの各ステップの状態を照合しない"],
  ["trace.rs", "                if !vec_eq(&t, &st.state) || !opt_eq(&o, &st.output) {", "                if !vec_eq(&t, &st.state) {",
   "トレースの各ステップの出力を照合しない"],
  ["trace.rs", "                    if ts.len() > 0 {\n                        return false;\n                    }\n", "",
   "有効な遷移があってもデッドロックとみなす"],
  ["trace.rs", "                Enumerated::Fail(_, _, _) => {\n                    return false;\n                },", "                Enumerated::Fail(_, _, _) => {},",
   "評価エラーのある状態をデッドロックとみなす"],
  ["trace.rs", "        Claim::Deadlock => c.deadlock && is_stuck(m, c, last) && result_is(&eval_terminal(m, last), false),",
   "        Claim::Deadlock => c.deadlock && is_stuck(m, c, last),", "終端の状態をデッドロックとみなす"],
  ["trace.rs", "        Claim::Invariant(i) => inv_on_exec(m, c, *i) && result_is(&eval_invariant(m, *i, last), false),",
   "        Claim::Invariant(i) => inv_on_exec(m, c, *i) && !result_is(&eval_invariant(m, *i, last), true),",
   "不変条件の評価エラーを違反とみなす"],
  ["trace.rs", "    if m.contracts[k].action != st.action {\n        return None;\n    }\n", "", "別の操作の契約を最後の遷移に適用する"],
  ["gate.rs", "                None => Verdict::of(VerdictKind::Verified),\n                Some(r) => Verdict::rejected(r),",
   "                None => Verdict::of(VerdictKind::Verified),\n                Some(r) => Verdict::of(VerdictKind::Verified),",
   "拒否した証明書で Verified を返す"],
  ["gate.rs", "            None => if is_violation_exec(claim) {\n                Verdict::of(VerdictKind::Violated)\n            } else {\n                Verdict::of(VerdictKind::Error)\n            },\n            Some(r) => Verdict::rejected(r),",
   "            None => Verdict::of(VerdictKind::Violated),\n            Some(r) => Verdict::rejected(r),",
   "評価エラーのトレースで Violated を返す"],
  ["gate.rs", "            Some(r) => Verdict::rejected(r),\n        },\n        Evidence::Unavailable",
   "            Some(r) => Verdict::of(VerdictKind::Violated),\n        },\n        Evidence::Unavailable",
   "拒否したトレースで Violated を返す"],
  ["gate.rs", "        Evidence::Unavailable(limit) => Verdict {\n            kind: VerdictKind::Inconclusive,",
   "        Evidence::Unavailable(limit) => Verdict {\n            kind: VerdictKind::Verified,", "証拠がないのに Verified を返す"],
  ["gate.rs", "        Err(e) => Verdict { kind: VerdictKind::InvalidModel, reject: None, invalid: Some(e), limit: None },\n        Ok(()) => decide_wf(m, c, ev),",
   "        Err(e) => decide_wf(m, c, ev),\n        Ok(()) => decide_wf(m, c, ev),", "IR検証に失敗したモデルを判定する"],
  ["gate.rs", "            match check_state(m, self.cond, states, k) {\n                Some(r) => {\n                    return Some(Verdict::rejected(r));\n                },\n                None => {},\n            }\n", "",
   "区切って進める証明書の検査で状態を調べない"],
  ["gate.rs", "        if k < states.len() {\n            return None;\n        }\n", "", "証明書を検査し終える前に Verified を返す"],
  ["gate.rs", "        match check_initials(m, &cert.states) {\n            Some(r) => Err(Verdict::rejected(r)),",
   "        match check_initials(m, &cert.states) {\n            Some(r) => Ok(CertCheck { model, cond: c, cert, next: 0 }),",
   "区切って進める証明書の検査で初期状態の欠けを見逃す"],
  ["gate.rs", "        Verdict { kind: VerdictKind::Inconclusive, reject: None, invalid: None, limit: Some(limit) }",
   "        Verdict { kind: VerdictKind::Verified, reject: None, invalid: None, limit: Some(limit) }", "打ち切った検査で Verified を返す"],
  ["mbt.rs", "            Seen::Value(x) => if x != s[var] {\n                return false;\n            },", "            Seen::Value(x) => {},", "観測した値を照合しない"],
  ["mbt.rs", "        (SeenOutput::Returned(Seen::Value(y)), Some(x)) => x == y,", "        (SeenOutput::Returned(Seen::Value(y)), Some(x)) => true,", "戻り値を照合しない"],
  ["mbt.rs", "                r.push(args[ks_exec[k]]);", "", "注入する選択の値を入力に含めない"],
  ["mbt.rs", "        if c == 0 {\n            assert(v0[mid as int]@ == t@);", "        if c <= 0 {\n            assert(v0[mid as int]@ == t@);", "等しくない状態を候補の列にあるとみなす"],
  ["mbt.rs", "                Enumerated::Fail(args, site, kind) => {\n                    return Err(ModelError { state: copy_vec(s), action: a, args, site, kind });\n                },\n                Enumerated::Ok(ts) => {\n                    if a == want {", "                Enumerated::Fail(args, site, kind) => {},\n                Enumerated::Ok(ts) => {\n                    if a == want {", "候補の更新で評価エラーを無視する"],
  ["mbt.rs", "                            l.push((a, x));", "", "状態で有効な入力を落とす"],
  ["mbt.rs", "                if has_input(&l, a, &common[k].1) {", "                if true {", "全候補で有効でない入力を残す"],
  ["mbt.rs", "            any = any || l.len() > 0;", "            any = false;", "有効な入力を持つ候補を見落とす"],
  ["mbt.rs", "            let ok = agrees_exec(&observed, &inits[i], seen);", "            let ok = true;", "初期観測を照合しない"],
  ["mbt.rs", "        if vec_eq(&xin, input) {", "        if true {", "入力の違う遷移で候補を更新する"],
  ["mbt.rs", "            if output_matches_exec(output, tr.output) && agrees_exec(obs, &tr.state, seen) {", "            if output_matches_exec(output, tr.output) {", "遷移先の観測を照合しない"],
  ["mbt.rs", "                insert_state(next, copy_vec(&tr.state));", "", "応答と一致する遷移先を候補に加えない"],
  ["mbt.rs", "                                *violation = Some((true, k, copy_vec(&tr.state)));", "                                *violation = Some((true, k, copy_vec(s)));", "不変条件の違反に遷移前の状態を記録する"],
  ["mbt.rs", "        while i < self.cands.states.len()\n", "        while i < self.cands.states.len() && i < 1\n", "2番目以降の候補を更新に使わない"],
  ["mbt.rs", "                Absorbed::TooMany => {\n                    return Update::TooMany;", "                Absorbed::TooMany => {\n                    return Update::Failure;", "候補数の上限超過を不適合とする"],
  ["mbt.rs", "                Absorbed::Disabled => {\n                    assert(s0.possible(s@));\n                    return Update::InvalidInput;\n                },", "                Absorbed::Disabled => {},", "入力が無効な候補を無視する"]
].freeze

# 到達点に置く assert(false)。[ファイル, 直前に挿入する位置の文字列, 説明]。
# 前提や不変条件が矛盾していて証明が空虚に通っているなら、ここの assert(false) も通ってしまう。
VERUS_CANARIES = [
  ["keys.rs", "        assert(pre.push(vs.last()) == vs);", "lemma_rank_seq_in_product の帰納"],
  ["keys.rs", "        assert(vs.drop_last() == p[q]);", "lemma_product_rank の帰納"],
  ["encoding.rs", "        assert(s.skip(prefix.len() as int) == last);", "lemma_models_enc_seq の帰納"],
  ["encoding.rs", "            assert(rows =~= Seq::new(n, |_i: int| None::<SVal>));", "lemma_default_len のMap"],
  ["encoding.rs", "            assert(n * w >= 1) by (nonlinear_arith)", "lemma_width_pos のMap"],
  ["eval.rs", "    to_bool(eval(e, c))\n}", "eval_prop"],
  ["eval.rs", "    if i < tys.len() && i < xs.len() {\n        Ok(decode_value(&tys[i], xs[i]))", "lookup_value"],
  ["eval.rs", "        assert(inner@.subrange(0, n as int) =~= ls@);\n        x = x + 1;", "quant のループの末尾"],
  ["eval.rs", "        (-(t as i128) - 1, d - (r0 as i128) - 1)", "pos_divmod の負の被除数"],
  ["eval.rs", "                eval_in(b, c, &inner)", "eval_in の let"],
  ["step.rs", "            match &act.output {\n                None => StepR::To(t, None),", "step の更新の後"],
  ["step.rs", "        v = v + 1;\n    }\n    assert(covers_prefix", "enum_rec のループの末尾"],
  ["step.rs", "    None\n}\n\n/// 状態 `s` での操作 `a` の有効な遷移を、引数の辞書順に列挙する。", "enum_rec の出口"],
  ["typing.rs", "    Ok(())\n}\n\n// ---- 型健全性", "validate_raw の受理"],
  ["typing.rs", "                        lemma_updates_typed(m, a, env, k + 1, acc2);", "lemma_updates_typed の再帰"],
  ["typing.rs", "    lemma_prop_typed(m.actions@[a].guard, t, env);", "lemma_step_typed"],
  ["typing.rs", "        lemma_quant_sound(all, ty, lo, hi, body, t, env, ls, lt, x + 1);", "lemma_quant_sound の再帰"],
  ["typing.rs", "                    lemma_type_sound_l(*b, t, env, ls.push(v), lt.push(x));", "let の型健全性"],
  ["cert.rs", "        lemma_reach_in_cert(m, c, cert, p, (n - 1) as nat);", "lemma_reach_in_cert の帰納"],
  ["cert.rs", "        assert(in_cert(cert, m.inits@[i]@));", "lemma_reach_in_cert の初期状態"],
  ["cert.rs", "            Ok(ts.len() > 0)", "check_action の受理"],
  ["cert.rs", "    if c.deadlock && !enabled {\n        match eval_terminal(m, s) {", "check_state の操作の後"],
  ["cert.rs", "    proof {\n        lemma_inductive_safe(*m, *c, cert@);\n    }\n    None", "check_certificate の受理"],
  ["trace.rs", "        assert(step_ok(*m, *c, start@, steps@, k as int));\n        k = k + 1;", "replay のステップの受理"],
  ["trace.rs", "    true\n}\n\nfn result_is", "is_stuck の受理"],
  ["trace.rs", "    if check_claim(m, c, start, steps, claim) {\n        None", "check_trace の受理"],
  ["gate.rs", "            match check_certificate(m, c, &cert.states) {", "decide の証明書の検査の前"],
  ["gate.rs", "    decide_wf(model.raw(), c, ev)\n}", "decide"],
  ["gate.rs", "    match validate_raw(m) {\n        Err(e) => Verdict {", "decide_raw"],
  ["gate.rs", "            k = k + 1;\n            left = left - 1;", "CertCheck::advance のループの末尾"],
  ["gate.rs", "        Some(Verdict::of(VerdictKind::Verified))\n    }", "CertCheck::advance の受理"],
  ["mbt.rs", "        Begun::Started(Session {", "Session::start の受理"],
  ["mbt.rs", "    Absorbed::Enabled\n}", "absorb の受理"],
  ["mbt.rs", "        Ok((common, any))\n", "common_inputs の受理"],
  ["mbt.rs", "            return Update::Failure;", "observe の不適合"],
  ["mbt.rs", "        self.cands = Candidates { states: next, hist: Ghost(h1) };", "observe の更新"],
  ["mbt.rs", "            assert(consistent(m, c, obs, inj, first, h1, t));", "lemma_next_exact の構成"]
].freeze

def verus_replace_once(text, from, to, what)
  count = text.scan(from).length
  abort "verus: #{what}: 置き換える箇所が #{count} 件ある（ちょうど1件でなければならない）。rakelib/verus.rake を更新する" unless count == 1
  text.sub(from) { to }
end

def verus_variant(name, file, description)
  dir = File.join(Dir.tmpdir, "fmspec-verus-#{Process.pid}", name)
  FileUtils.mkdir_p(dir)
  FileUtils.cp_r(File.join(VERUS_CRATE, "src"), dir)
  path = File.join(dir, "src", file)
  File.write(path, yield(File.read(path)))
  ok, verified, errors, out = verus_run(dir)
  if ok || errors.nil? || errors.zero?
    reason = errors.nil? && !ok ? "検証まで進まなかった" : "証明が通ってしまった"
    return "#{file}: #{description}: #{reason}\n#{out.lines.last(15).join}"
  end
  nil
ensure
  FileUtils.rm_rf(dir) if dir
end

def verus_parallel(jobs)
  queue = Queue.new
  jobs.each { |j| queue << j }
  failures = Queue.new
  Array.new(4) do
    Thread.new do
      loop do
        job = begin
          queue.pop(true)
        rescue ThreadError
          break
        end
        failure = job.call
        failures << failure if failure
      end
    end
  end.each(&:join)
  Array.new(failures.size) { failures.pop }
end

namespace :verus do
  desc "Verus のバージョンが固定したものと一致することを確かめる"
  task :version do
    out, = Open3.capture2e(verus_bin, "--version")
    version = out[/Version: (\S+)/, 1]
    abort "verus: #{verus_bin} のバージョンは #{version.inspect}。固定したバージョンは #{VERUS_VERSION}" unless version == VERUS_VERSION
  end

  desc "信頼する項目（assume、external_body など）が中核にないことを確かめる"
  task :trusted do
    VERUS_SOURCES.each do |path|
      found = verus_code(path).scan(VERUS_TRUST)
      abort "verus: #{path} に信頼する項目がある: #{found.uniq.join(', ')}" unless found.empty?
    end
    puts "verus: 信頼する項目は0件"
  end

  desc "証明の対象外のコードが、決めたファイルの外にないことを確かめる"
  task :coverage do
    VERUS_SOURCES.each do |path|
      name = File.basename(path)
      next if name == "lib.rs"

      code = File.read(path)
      inside = code.include?("verus! {")
      abort "verus: #{name} は証明の対象外のはずだが verus! ブロックがある" if VERUS_UNVERIFIED.include?(name) && inside
      next if VERUS_UNVERIFIED.include?(name)

      abort "verus: #{name} に verus! ブロックがない" unless inside
      # verus! の外には、use と属性と空行しか置かない。
      abort "verus: #{name} の verus! ブロックは1つにまとめる" unless code.scan(/^verus! \{$/).length == 1
      before, rest = code.split(/^verus! \{$/, 2)
      outside = before + rest.split(/^\} \/\/ verus!$/, 2).last.to_s
      stray = outside.lines.map(&:strip).reject { |l| l.empty? || l.start_with?("use ", "#[", "//") }
      abort "verus: #{name} の verus! の外にコードがある: #{stray.first(3).join(' / ')}" unless stray.empty?
    end
    puts "verus: 証明の対象外は #{VERUS_UNVERIFIED.join(', ')} だけ"
  end

  desc "公開関数が前提条件を持たないことを確かめる"
  task :contract do
    VERUS_SOURCES.each do |path|
      lines = verus_code(path).lines.map(&:rstrip)
      lines.each_with_index do |line, i|
        next unless line.strip.match?(/\Apub fn \w+/)

        signature = lines[i..].take_while { |l| l.strip != "{" && !l.end_with?(" {") }
        next unless signature.any? { |l| l.strip == "requires" }

        abort "verus: #{path}:#{i + 1}: 公開関数 #{line.strip[/pub fn (\w+)/, 1]} が requires を持つ。" \
              "未検証コードから呼べる関数は、必要な条件を自分で検査する"
      end
    end
    puts "verus: 公開関数は前提条件を持たない"
  end

  desc "検査を壊した変異と assert(false) が、証明に失敗することを確かめる"
  task mutants: :version do
    jobs = VERUS_MUTANTS.each_with_index.map do |(file, from, to, description), n|
      -> { verus_variant("mutant#{n}", file, description) { |src| verus_replace_once(src, from, to, description) } }
    end
    jobs += VERUS_CANARIES.each_with_index.map do |(file, anchor, description), n|
      lambda do
        verus_variant("canary#{n}", file, "assert(false): #{description}") do |src|
          verus_replace_once(src, anchor, "assert(false);\n#{anchor}", description)
        end
      end
    end
    failures = verus_parallel(jobs)
    unless failures.empty?
      puts failures
      abort "verus: #{failures.length} 件の変異または assert(false) が証明を通った。証明が検査を捉えていない"
    end
    puts "verus: 変異 #{VERUS_MUTANTS.length} 件と assert(false) #{VERUS_CANARIES.length} 件は、すべて証明に失敗した"
  end
end

desc "中核の証明を検証する（Verus #{VERUS_VERSION} が必要）"
task verus: %w[verus:version verus:trusted verus:coverage verus:contract] do
  ok, verified, errors, out = verus_run(VERUS_CRATE)
  puts out.lines.grep(/verification results|^(error|warning)/)
  abort "verus: 証明に失敗した\n#{out}" unless ok && errors&.zero?
  abort "verus: 警告がある\n#{out}" if out.match?(/^warning/)
  puts "verus: #{verified} 件を検証した"
  Rake::Task["verus:mutants"].invoke
end
