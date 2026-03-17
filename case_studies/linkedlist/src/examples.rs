
use super::List;


#[rr::returns("max_list_Z (min_int i32) v")]
fn max_list_i32(v: &List<i32>) -> i32 {
    let mut m = i32::MIN;

    for x in v {
        #[rr::inv_vars("m")]
        #[rr::inv("m = max_list_Z (min_int i32) {Hist}")]
        #[rr::ignore] ||{};

        m = m.max(*x);
    }

    m
}

#[rr::exists("MIN" : "{xt_of Self}")]
#[rr::exists("MIN_minimal" : "∀ x, {Self::Ord} {MIN} x ≠ Greater")]
trait Min : Ord {
    #[rr::returns("{MIN}")]
    fn minimum() -> Self;
}

#[rr::returns("max_list_cmp_def {T::Ord} {T::MIN} v")]
fn max_list<T>(v: &List<T>) -> T 
    where T: Ord + Min + Copy
{
    let mut m = T::minimum();

    for x in v {
        #[rr::inv_vars("m")]
        #[rr::inv("m = max_list_cmp_def {T::Ord} {T::MIN} {Hist}")]
        #[rr::ignore] ||{};

        m = m.max(*x);
    }

    m
}
