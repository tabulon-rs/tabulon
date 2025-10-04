/// 표현식을 구성하는 AST 노드들.
/// 모든 중간 값과 최종 결과는 f64로 표현되며,
/// 비교/논리의 결과는 true=1.0, false=0.0으로 반환됩니다.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Ast {
    /// 숫자 리터럴 (예: 1, 3.14)
    Num(f64),
    /// 변수 참조 (예: Str, BonusStr)
    Var(String),
    /// 단항 음수 (예: -x)
    Neg(Box<Ast>),
    /// 덧셈 (a + b)
    Add(Box<Ast>, Box<Ast>),
    /// 뺄셈 (a - b)
    Sub(Box<Ast>, Box<Ast>),
    /// 곱셈 (a * b)
    Mul(Box<Ast>, Box<Ast>),
    /// 나눗셈 (a / b)
    Div(Box<Ast>, Box<Ast>),
    /// 동등 비교 (a == b)
    Eq(Box<Ast>, Box<Ast>),
    /// 비동등 비교 (a != b)
    Ne(Box<Ast>, Box<Ast>),
    /// 보다 작음 (a < b)
    Lt(Box<Ast>, Box<Ast>),
    /// 작거나 같음 (a <= b)
    Le(Box<Ast>, Box<Ast>),
    /// 보다 큼 (a > b)
    Gt(Box<Ast>, Box<Ast>),
    /// 크거나 같음 (a >= b)
    Ge(Box<Ast>, Box<Ast>),
    /// 논리 AND (a && b) — 0.0이 아닌 값을 true로 간주합니다.
    And(Box<Ast>, Box<Ast>),
    /// 논리 OR (a || b) — 0.0이 아닌 값을 true로 간주합니다.
    Or(Box<Ast>, Box<Ast>),
    /// 조건식 if(cond, then, else) — cond >= 1.0이면 then, cond == 0.0이면 else를 반환합니다.
    If(Box<Ast>, Box<Ast>, Box<Ast>),
    /// 최대값 함수 max(a, b) — 두 인자 중 더 큰 값을 반환합니다.
    Max(Box<Ast>, Box<Ast>),
    /// 최소값 함수 min(a, b) — 두 인자 중 더 작은 값을 반환합니다.
    Min(Box<Ast>, Box<Ast>),
    /// 일반 함수 호출 name(args..). 함수명은 변수 목록에서 제외됩니다.
    Call { name: String, args: Vec<Ast> },
}
