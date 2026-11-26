# frozen_string_literal: true

# 中核（crates/fmspec-core）の Verus による検証（仕様書 §14.1、§14.3）。
#
# `rake verus` は、証明を通すだけでなく、証明が空虚でないことも検査する。
#
# - verus:trusted   信頼する項目（assume、admit、external_body など）が1つもない。
# - verus:contract  未検証コードから呼べる公開関数が、前提条件（requires）を持たない（仕様書 §3.1）。
# - verus:mutants   検査を1つ壊した変異と、到達点に assert(false) を置いた変種が、証明に失敗する。
#
# `rake verus:proof` は、変異の検査を除いて、証明とその他の検査だけを行う。
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
  ["infer.rs", "BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Some(XType::Bool),",
   "BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Some(XType::Int),", "比較の型を整数にする"],
  ["encoding.rs", "(SType::Int(l1, h1), SType::Int(l2, h2)) => *l1 == *l2 && *h1 == *h2,",
   "(SType::Int(l1, h1), SType::Int(l2, h2)) => *l1 == *l2,", "整数の型の上端を比べない"],
  ["encoding.rs", "        SType::Option(x) => match keys_exec(x, enums) {\n            Some(k) => Some(k + 1),",
   "        SType::Option(x) => match keys_exec(x, enums) {\n            Some(k) => Some(k),", "Optionの値の数に空を数えない"],
  ["encoding.rs", "            if names[j] == names[i] {", "            if names[j] == names[i] && j > 0 {",
   "名前の重複検査で先頭を比べない"],
  ["keys.rs", "p[i / d.len() as int].push(d[i % d.len() as int])", "p[i % p.len() as int].push(d[i / p.len() as int])",
   "Tupleの正規順で最初の要素を最も速く変える"],
  ["keys.rs", "seq![SVal::None] + domain(*x, enums).map_values(|v: SVal| SVal::Some(Box::new(v))),",
   "domain(*x, enums).map_values(|v: SVal| SVal::Some(Box::new(v))) + seq![SVal::None],", "Optionの空を最後に並べる"],
  ["keys.rs", "(STy::Int(lo, _), SVal::Int(x)) => x - lo,", "(STy::Int(lo, _), SVal::Int(x)) => x as int,", "整数の番号から下端を引かない"],
  ["encoding.rs", "        STy::Option(x) => 1 + width(*x, enums),", "        STy::Option(x) => width(*x, enums),",
   "Optionの幅に有無のスロットを数えない"],
  ["encoding.rs", "SVal::List(items) => seq![Value::Int(items.len() as i64)] + enc_items(", "SVal::List(items) => enc_items(",
   "Listの符号化に長さを入れない"],
  ["encoding.rs", "        STy::Enum(id) => id < enums.len() && enums[id as int] >= 1,",
   "        STy::Enum(id) => id < enums.len() && enums[id as int] >= 0,", "ラベルのない列挙型を整形式とする"],
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
  ["mbt.rs", "                Absorbed::Disabled => {\n                    assert(s0.possible(s@));\n                    return Update::InvalidInput;\n                },", "                Absorbed::Disabled => {},", "入力が無効な候補を無視する"],
  ["lowering.rs", "let (t, out) = layout_slots(&cx.args[*i], 2, enums)?;", "let (t, out) = layout_slots(&cx.args[*i], 0, enums)?;", "引数を状態変数として参照する"],
  ["lowering.rs", "*k < enums[*id]) {", "*k <= enums[*id]) {", "範囲外の列挙型のラベルを受け入れる"],
  ["lowering.rs", "let x = wrap(&blk.binds, copy_expr(&slots[0]));", "let x = copy_expr(&slots[0]);", "スカラーの下ろしで束縛を捨てる"],
  ["slots.rs", "let e = ite(copy_expr(&in_dom), copy_expr(&r), ci(-1));", "let e = ite(copy_expr(&in_dom), copy_expr(&r), ci(0));", "型に属さないキーの番号を0にする"],
  ["slots.rs", "let y = bin(BinOp::Le, copy_expr(&slots[0]), ci(*hi));", "let y = bin(BinOp::Lt, copy_expr(&slots[0]), ci(*hi));", "整数の型の上限を除く"],
  ["lowering.rs", "let r = lookup_rank(x, cx, sc, blk, &k)?;\n    let ghost b2", "let r = lookup_rank(x, cx, sc, blk, &v)?;\n    let ghost b2", "Mapのキーの番号を値の型で計算する"],
  ["lowering.rs", "out.push(bin(*op, x, y));", "out.push(bin(*op, y, x));", "比較の左右を入れ替える"],
  ["lowering.rs", "out.push(not(x));", "out.push(x);", "否定を落とす"],
  ["lowering.rs", "out.push(bind(blk, Expr::Implies(Box::new(p), Box::new(q)))?);", "out.push(bind(blk, Expr::Or(Box::new(p), Box::new(q)))?);", "含意を論理和にする"],
  ["lowering.rs", "if all { Join::RawAnd } else { Join::RawOr }", "if all { Join::RawOr } else { Join::RawAnd }", "allとanyのたたみ方を入れ替える"],
  ["lowering.rs", "let out = ite_slots(&c, &xs, &ys, d)?;", "let out = ite_slots(&c, &ys, &xs, d)?;", "条件式の枝を入れ替える"],
  ["quant.rs", "out.push(bin(BinOp::Add, copy_expr(r), ci(*lo)));", "out.push(bin(BinOp::Sub, copy_expr(r), ci(*lo)));", "整数の番号に下端を足さない"],
  ["quant.rs", "acc = ite(eq(copy_expr(r), ci(k)), Expr::Const(Value::Enum(id, k)), acc);", "acc = ite(eq(copy_expr(r), ci(k)), Expr::Const(Value::Enum(id, 0)), acc);", "列挙型の番号をラベルに対応させない"],
  ["quant.rs", "payload.push(ite(eq(copy_expr(r), ci(0)), copy_expr(&ds[j]), copy_expr(&us[j])));", "payload.push(ite(eq(copy_expr(r), ci(0)), copy_expr(&us[j]), copy_expr(&ds[j])));", "Optionの番号0で中身を作る"],
  ["quant.rs", "let pre = unrank_seq(_parent, ts, n - 1, &q, enums)?;", "let pre = unrank_seq(_parent, ts, n - 1, &m, enums)?;", "組の先頭の番号に剰余を使う"],
  ["quant.rs", "let x = ite(c, a, b);", "let x = ite(c, b, a);", "印を選ぶ木の枝を入れ替える"],
  ["lowering.rs", "Expr::Implies(Box::new(guard), Box::new(e))", "Expr::And(Box::new(guard), Box::new(e))", "forallのガードを論理積にする"],
  ["lowering.rs", "let at = j.checked_mul(stride)?;", "let at = j.checked_mul(w)?;", "Mapの有無の位置を値の幅で数える"],
  ["lowering.rs", "let hi = n as i64 - 1;", "let hi = n as i64 - 2;", "量化で最後の値をたどらない"],
  ["lowering.rs", "(copy_stype(t), cb(true), n as usize, us)", "(copy_stype(t), cb(false), n as usize, us)", "型の全体をたどる量化で値を選ばない"],
  ["lowering.rs", "let g = bin(BinOp::Lt, Expr::Local(d), copy_expr(&cs[0]));", "let g = bin(BinOp::Le, Expr::Local(d), copy_expr(&cs[0]));", "Listの長さの位置まで要素とみなす"],
  ["lowering.rs", "let at = k.checked_mul(w)?.checked_add(1)?.checked_add(j)?;", "let at = k.checked_mul(w)?.checked_add(j)?;", "Listの長さのスロットを要素のスロットとみなす"],
  ["lowering.rs", "bits = mark(&bits, &r, true);", "bits = mark(&bits, &r, false);", "Setのリテラルの要素に印を付けない"],
  ["lowering.rs", "out.push(and(bin(BinOp::Ge, r, ci(0)), hit));", "out.push(hit);", "型に属さない要素の番号でSetのスロットを選ぶ"],
  ["lowering.rs", "let out = mark(&bits, &r, true);", "let out = mark(&bits, &r, false);", "Setに要素を加えずに除く"],
  ["lowering.rs", "let out = mark(&bits, &r, false);", "let out = mark(&bits, &r, true);", "Setから要素を除かずに加える"],
  ["lowering.rs", "let pos = j.checked_mul(stride)?;", "let pos = j.checked_mul(w)?;", "Mapの大きさで有無の位置を値の幅で数える"],
  ["lowering.rs", "out.push(not(any_of(&flags)));", "out.push(any_of(&flags));", "空かの判定を反転する"],
  ["lowering.rs", "out.push(eq(len, ci(0)));", "out.push(eq(len, ci(1)));", "Listが空かを長さ1と比べる"],
  ["lowering.rs", "                if *positive {", "                if !*positive {", "等しさと等しくなさを入れ替える"],
  ["slots.rs", "Some(and(eq(copy_expr(&x[0]), copy_expr(&y[0])), implies(copy_expr(&x[0]), rest)))", "Some(implies(copy_expr(&x[0]), rest))", "Optionの有無を比べない"],
  ["slots.rs", "XType::List(e, max) => *max <= 0x7fff_ffffusize && small_stype(e),", "XType::List(e, _) => small_stype(e),", "Listの長さの上限を確かめずに等しさを比べる"],
  ["equality.rs", "SType::List(e, max) => *max <= 0x7fff_ffffusize && small_stype(e),", "SType::List(e, _) => small_stype(e),", "入れ子のListの長さの上限を確かめない"],
  ["lowering.rs", "out.push(ci(es.len() as i64));", "out.push(ci(0));", "Listのリテラルの長さを0にする"],
  ["lowering.rs", "while p < *max", "while p + 1 < *max", "Listのリテラルを上限まで埋めない"],
  ["lowering.rs", "let cond = and(bin(BinOp::Ge, copy_expr(&i), ci(0)), bin(BinOp::Lt, copy_expr(&i), len));", "let cond = and(bin(BinOp::Ge, copy_expr(&i), ci(0)), bin(BinOp::Le, copy_expr(&i), len));", "添字の範囲に長さを含める"],
  ["lowering.rs", "copy_exprs(&rows[0])", "copy_exprs(&rows[rows.len() - 1])", "Listの先頭の代わりに最後の行を返す"],
  ["lowering.rs", "let i = bind(blk, bin(BinOp::Sub, len, ci(1)))?;", "let i = bind(blk, bin(BinOp::Sub, len, ci(0)))?;", "Listの末尾の添字を長さにする"],
  ["lowering.rs", "check(blk, bin(BinOp::Lt, copy_expr(&len), ci(max as i64)), FAIL_FULL)?;", "check(blk, bin(BinOp::Le, copy_expr(&len), ci(max as i64)), FAIL_FULL)?;", "満杯のListに要素を加える"],
  ["lowering.rs", "let new_len = bind(blk, bin(BinOp::Add, copy_expr(&len), ci(1)))?;", "let new_len = bind(blk, bin(BinOp::Add, copy_expr(&len), ci(0)))?;", "要素を加えても長さを増やさない"],
  ["lowering.rs", "let out = ite_rows(&rows, &new_len, &defs)?;", "let out = ite_rows(&rows, &ci(0), &defs)?;", "末尾でなく先頭の行を既定値にする"],
  ["lowering.rs", "let mut p = 1;", "let mut p = 0;", "Listの先頭を除かずに詰める"],
  ["lowering.rs", "hits.push(and(bin(BinOp::Gt, copy_expr(&len), ci(p as i64)), same));", "hits.push(same);", "Listの長さより後ろの行も比べる"],
  ["lowering.rs", "if !xtype_eq(&tx, &et) {", "if !xtype_eq(&tx, &tx) {", "Listの要素と値の型を確かめずに比べる"],
  ["lowering.rs", "out.push(and(known, hit));", "out.push(hit);", "型に属さないキーの番号でMapの行を選ぶ"],
  ["lowering.rs", "alt.push(cb(false));", "alt.push(cb(true));", "Mapから除いたキーを有りのままにする"],
  ["lowering.rs", "alt.push(cb(true));", "alt.push(cb(false));", "Mapに置いたキーを無しにする"],
  ["lowering.rs", "if keys_exec(k, enums).is_none() {", "if keys_exec(k, enums).is_none() && items.len() > 0 {", "キーの数が決まらない型の空のMapを下ろす"],
  ["slots.rs", "c.push(copy_expr(&rows[t][j]));", "c.push(copy_expr(&rows[0][j]));", "どの添字でもListの先頭の行を選ぶ"],
  ["slots.rs", "        let start = p.checked_mul(w)?.checked_add(1)?;\n        let end = start.checked_add(w)?;\n        if end > slots.len() {\n            return None;\n        }\n        let ghost i0", "        let start = p.checked_mul(w)?;\n        let end = start.checked_add(w)?;\n        if end > slots.len() {\n            return None;\n        }\n        let ghost i0", "Listの長さのスロットを行に含める"],
  ["slots.rs", "if size != slots.len() {", "if size > slots.len() {", "Mapのスロットの長さを確かめない"],
  ["slots.rs", "vs.push(ite(eq(copy_expr(k), ci(p as i64)), copy_expr(&alt[j]), copy_expr(&rows[p][j])));", "vs.push(ite(eq(copy_expr(k), ci(p as i64)), copy_expr(&rows[p][j]), copy_expr(&alt[j])));", "行の置き換えを逆にする"],
  ["canon.rs", "ite(copy_expr(&slots[0]), inner, empty)", "ite(copy_expr(&slots[0]), empty, inner)", "Optionの有無と中身の判定を入れ替える"],
  ["canon.rs", "if is_bool_lit(&inner, true) && is_bool_lit(&empty, true) {", "if is_bool_lit(&inner, true) {", "Optionの中身が既定値かを確かめずに真にする"],
  ["canon.rs", "items.push(ite(copy_expr(&row[0]), c, empty));", "items.push(c);", "Mapのキーのない行の値を確かめない"],
  ["canon.rs", "items.push(ite(bin(BinOp::Lt, ci(p as i64), copy_expr(&len)), c, empty));", "items.push(ite(bin(BinOp::Le, ci(p as i64), copy_expr(&len)), c, empty));", "Listの長さの位置の行を要素として判定する"],
  ["canon.rs", "items.push(eq(copy_expr(&xs[i]), copy_expr(&ys[i])));", "items.push(eq(copy_expr(&xs[i]), copy_expr(&xs[i])));", "既定値と比べない"],
  ["canon.rs", "items.push(canonical(&ts[i], &parts[i], enums)?);", "items.push(canonical(&ts[0], &parts[i], enums)?);", "組の各要素を最初の要素の型で判定する"],
  ["canon.rs", "STy::List(e, max) => seq![Type::Int(0, max as i64)]", "STy::List(e, max) => seq![Type::Int(1, max as i64)]", "Listの長さのスロットの型から0を除く"],
  ["canon.rs", "(Type::Int(lo, hi), Value::Int(k)) => lo <= k <= hi,", "(Type::Int(lo, hi), Value::Int(k)) => true,", "整数のスロットの範囲を確かめない"],
  ["smodel.rs", "g = Expr::And(Box::new(c), Box::new(g));", "g = Expr::Or(Box::new(c), Box::new(g));", "引数の正規形の判定を `||` でつなぐ"],
  ["smodel.rs", "        if out.len() == 0 {\n            return Err(LowerError::Update(a, u));", "        if out.len() == usize::MAX {\n            return Err(LowerError::Update(a, u));", "スロットのない代入を受け入れる"],
  ["smodel.rs", "let target = match off.checked_add(j) {", "let target = match off.checked_add(j + 1) {", "代入を1つ後ろのスロットに書く"],
  ["smodel.rs", "if out.len() != 1 {", "if out.len() == 0 {", "出力のスロットの数を確かめない"],
  ["smodel.rs", "SType::Int(lo, hi) => Type::Int(*lo, *hi),", "SType::Int(lo, hi) => Type::Int(*lo, *lo),", "出力の整数の範囲を変える"],
  ["smodel.rs", "let domains = slot_types_list(&sa.args, &cx.enums);", "let domains: Vec<Type> = Vec::new();", "操作のドメインを空にする"],
  ["model_lower.rs", "            Ok(false) => {},\n            Ok(true) => {", "            Ok(true) => {},\n            Ok(false) => {", "初期条件が偽の状態を残す"],
  ["model_lower.rs", "let x = concat(&ps[p], &cs[q]);", "let x = concat(&cs[q], &ps[p]);", "候補の符号を逆の順につなぐ"],
  ["model_lower.rs", "if k < out.len() && vec_eq(&out[k], &x) {", "if k < out.len() {", "等しくない候補を捨てる"],
  ["model_lower.rs", "    if out.len() == 0 {\n        return Err(Fault::Lower);", "    if out.len() == usize::MAX {\n        return Err(Fault::Lower);", "スロットのない値を評価済みとする"],
  ["model_lower.rs", "cx.consts.push(Constant { ty: copy_stype(&c.ty), slots: vals });", "cx.consts.push(Constant { ty: copy_stype(&c.ty), slots: Vec::new() });", "定数のスロットを空にする"],
  ["model_lower.rs", "    cx.next = true;", "    cx.next = false;", "遷移契約から遷移後の状態を参照できなくする"],
  ["model_lower.rs", "Some(o) => Some(copy_stype(&o.ty)),", "Some(_) => None,", "遷移契約から出力を参照できなくする"],
  ["model_lower.rs", "ls.push(Layout { ty: copy_stype(&ts[i]), offset: off });", "ls.push(Layout { ty: copy_stype(&ts[i]), offset: 0 });", "どの位置も0にする"],
  ["model_lower.rs", "if !(wf_stype_exec(&ts[i], enums) && small_stype(&ts[i])) {", "if !wf_stype_exec(&ts[i], enums) {", "Listの長さの上限を確かめない"],
  ["canon.rs", "out.push(Type::Int(0, *max as i64));", "out.push(Type::Int(1, *max as i64));", "スロットの型の実装でListの長さから0を除く"]
].freeze

# 到達点に置く assert(false)。[ファイル, 直前に挿入する位置の文字列, 説明]。
# 前提や不変条件が矛盾していて証明が空虚に通っているなら、ここの assert(false) も通ってしまう。
VERUS_CANARIES = [
  ["infer.rs", "            assert(decreases_to!(*_parent => item.value));", "check_items のループ"],
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
  ["mbt.rs", "            assert(consistent(m, c, obs, inj, first, h1, t));", "lemma_next_exact の構成"],
  ["lowering.rs", "assert(key_rank(l3, rank_local) == rk as int);", "lemma_get のキーの番号"],
  ["lowering.rs", "assert(store_ok(_c, stored@, env, l, v, sty(*st), se.enums));", "lower_stored の値の場合"],
  ["lowering.rs", "assert(slot_vals(slots@, env, l) =~= seq![eval_l(slots@[0], env, l)->Ok_0]);", "scalar_in の値の場合"],
  ["lowering.rs", "            assert(ctx_ok(cx, sc2, env, se, l2, sls2));", "lemma_let の局所変数の対応"],
  ["lowering.rs", "                lemma_fold_eq(all, es@, terms, se, sls, env, l);", "lemma_fold の値の場合"],
  ["lowering.rs", "                    assert(lk.take((d + j) as int) =~= lj);", "lemma_ite_prefix の帰納"],
  ["preserve.rs", "        assert(s.skip(cut) =~= mix2(a.skip(cut), b.skip(cut), m.skip(cut)));", "lemma_models_seq_mix の帰納"],
  ["preserve.rs", "        assert(v1.drop_last() =~= v0);", "lemma_mixed_eval の帰納"],
  ["lowering.rs", "            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, 0);", "lemma_quant の値の場合"],
  ["lowering.rs", "        lemma_guard_pick(g, fs, bits, env, l);", "lemma_over_map_at の値の場合"],
  ["lowering.rs", "            lemma_list_quant_at(st, max, w, cs, us, g, items, env, l, enums);", "lemma_over_list の値の場合"],
  ["lowering.rs", "        lemma_models_enc(item, st, enums);", "lemma_list_quant_at の要素"],
  ["lowering.rs", "        lemma_scalar_bool(eval_src(body, se, sls2), eval_l(b, env, lx), se.enums);", "lemma_quant_step の選ぶ位置"],
  ["quant.rs", "            lemma_qscan(all, ty, qb, env, l, bits, dom, body, se, sls, n + 1);", "lemma_qscan の帰納"],
  ["lowering.rs", "                    lemma_setlit_step(es@.take(i + 1), *cx, sc0, b0, b1, *blk, sty(*t), bv, r, bits@);", "Setのリテラルのループ"],
  ["lowering.rs", "                    lemma_mark(true, bits, r, out, p, i as i64, env, l2);\n                    let q", "lemma_insert の値の場合"],
  ["lowering.rs", "                lemma_count_none(bits);", "lemma_is_empty の空の場合"],
  ["lowering.rs", "            lemma_count_some(v->Map_0);\n            }\n            lemma_one_denotes(x, env, l2", "lemma_size のMap"],
  ["lowering.rs", "                lemma_one_denotes(out[0], env, l, Value::Bool((va == vb) == positive), XTy::Bool, se.enums);", "lemma_eq の値の場合"],
  ["equality.rs", "            lemma_inj_items(i1, i2, *e, enums);", "lemma_enc_inj のList"],
  ["equality.rs", "            lemma_kinds_rows(rows, *x, enums);", "lemma_kinds のMap"],
  ["equality.rs", "            lemma_enc_inj(vx, vy, st, enums);", "lemma_eq_coll の等しい場合"],
  ["equality.rs", "            lemma_and(e0, imp, env, l, true, w1 == w2);", "lemma_eq_option の中身がある場合"],
  ["lowering.rs", "assert(slot_vals(out, env, l2) =~= seq![Value::Int(n)] + enc_items(items, st, enums));", "lemma_listlit_step の値の場合"],
  ["lowering.rs", "lemma_clean_concat(o2, lits(tail), env, l);", "lemma_listlit_done の値の場合"],
  ["lowering.rs", "lemma_select(rows, y, out, pad_vals(items, st, max as nat, enums), env, l4, n);", "lemma_at の範囲内の場合"],
  ["lowering.rs", "lemma_items_member(items, st, enums, 0);", "lemma_first の値の場合"],
  ["lowering.rs", "lemma_select(rows, i, out, pad_vals(items, st, max as nat, enums), env, l3, n);", "lemma_last の値の場合"],
  ["lowering.rs", "lemma_list_join(new_len, out, env, l4, items2, st, max, enums);", "lemma_push の値の場合"],
  ["lowering.rs", "lemma_ite_rows(out, rows, new_len, defs, pad_vals(items, st, max as nat, enums), dv, env, l3, (m - 1) as i64);", "lemma_pop の値の場合"],
  ["lowering.rs", "lemma_items_drop_first(items, st, enums);", "lemma_shift の値の場合"],
  ["lowering.rs", "lemma_any_of(hits, env, l2);", "lemma_list_contains の値の場合"],
  ["lowering.rs", "lemma_none_rows(keys_or_zero(kt, enums), vt, enums);", "lemma_maplit_base"],
  ["lowering.rs", "assert(denotes(s1, env, l1, SVal::Map(rows), XTy::Map(Box::new(kt), Box::new(vt)), se.enums));", "lemma_maplit_step の値の場合"],
  ["lowering.rs", "lemma_rows_update(rows, vt, enums, rk as int, Some(vv));", "lemma_put の値の場合"],
  ["lowering.rs", "assert(denotes(ms, env, l1, SVal::Map(rows), mt, se.enums));", "lemma_put_expr の値の場合"],
  ["lowering.rs", "assert(slot_vals(h, env, l1) =~= enc(SVal::Set(bits), STy::Set(Box::new(kt)), enums));", "lemma_keys の値の場合"],
  ["lowering.rs", "assert(eval_src(e, se, sls) == eval_src(es, se, sls));", "lemma_has_key の意味の一致"],
  ["lowering.rs", "lemma_rows_update(rows, vt, enums, rkk, None);", "lemma_delete のキーがある場合"],
  ["maps.rs", "lemma_enc_rows_index(rows, vt, enums, p, j);", "lemma_map_parts の各スロット"],
  ["maps.rs", "lemma_flat_rows(a, b, t, env, l, enums);", "lemma_flat_rows の帰納"],
  ["maps.rs", "lemma_rows_update(rows.drop_last(), t, enums, r, o);", "lemma_rows_update の帰納"],
  ["lists.rs", "assert(slot_vals(out[p], env, l) =~= nv[p]);", "lemma_ite_rows の各行"],
  ["lists.rs", "lemma_flat(a, b, st, env, l, enums);", "lemma_flat の帰納"],
  ["slots.rs", "assert(ite_row(out@[p as int]@, rows@[p as int]@, *k, alt@, p as int));", "ite_rows のループ"],
  ["slots.rs", "rows.push(sub_exprs(slots, at, end));", "map_rows のループ"],
  ["canon.rs", "        lemma_map_join(rows, env, ls, rs, k, x, enums);", "lemma_canon_map_eval の正規形の組み立て"],
  ["canon.rs", "        lemma_list_join(len, rows, env, ls, its, e, max, enums);", "lemma_canon_list_eval の正規形の組み立て"],
  ["canon.rs", "        lemma_concat_split(slots, parts, xts, enums);", "lemma_canon_tuple_eval の正規形の組み立て"],
  ["canon.rs", "        let v = SVal::Some(Box::new(w));", "lemma_canon_option_vals の中身のある値"],
  ["canon.rs", "        lemma_flat_split(t, a, w);", "lemma_flat_split の帰納"],
  ["canon.rs", "            lemma_ty_repeat_add(et, n, m);", "lemma_member_in のList"],
  ["canon.rs", "                lemma_in_member(*w, *x, enums);", "lemma_in_member のOption"],
  ["canon.rs", "        lemma_in_member(vs.last(), ts.last(), enums);", "lemma_in_members の帰納"],
  ["lowering.rs", "                            lemma_in_member(v, sty(*st), se.enums);", "lower_stored の型に属する値"],
  ["smodel.rs", "    lemma_out(sa.output, cx, m, a, env, se);", "lemma_step の出力"],
  ["model_safe.rs", "    lemma_env_act(sm, cv, m, st, cs[a], a, p, ps, vs, xs);", "lemma_trans の環境"],
  ["model_safe.rs", "    if safe(m, c) {", "lemma_safe"],
  ["model_safe.rs", "        lemma_reach_core(sm, cv, m, st, cs, ks, sx, c, q, (n - 1) as nat);", "lemma_reach_core の帰納"],
  ["model_lower.rs", "    assert(ts.take(n) =~= ts);", "lemma_init_ok"],
  ["model_lower.rs", "        lemma_init_ok(*sm, cv, m, stg, sx, psg, cc);", "lower_model の結論"],
  ["model_lower.rs", "            lemma_prod_step(*sm, cv, k as int, ps@, cands@[k as int]@, next@);", "lower_model の候補の直積"]
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

namespace :verus do
  # 変異と assert(false) の検査（verus:mutants）を除いたもの。CI では push と PR ごとにこれを実行し、
  # 変異の検査は main への PR と定期実行で行う（.github/workflows/ci.yml）。
  desc "中核の証明だけを検証する（変異と assert(false) の検査を除く）"
  task proof: %w[verus:version verus:trusted verus:coverage verus:contract] do
    ok, verified, errors, out = verus_run(VERUS_CRATE)
    puts out.lines.grep(/verification results|^(error|warning)/)
    abort "verus: 証明に失敗した\n#{out}" unless ok && errors&.zero?
    abort "verus: 警告がある\n#{out}" if out.match?(/^warning/)
    puts "verus: #{verified} 件を検証した"
  end
end

desc "中核の証明と、証明が空虚でないことの検査（Verus #{VERUS_VERSION} が必要）"
task verus: %w[verus:proof verus:mutants]
