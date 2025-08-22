// Test case for the lifetime trait issue
trait LifetimeTrait {
    type Ty;
    fn lifetime_method<'a>(&self, arg: &'a Self::Ty) -> &'a Self::Ty;
}

impl LifetimeTrait for i32 {
    type Ty = i32;
    fn lifetime_method<'a>(&self, arg: &'a Self::Ty) -> &'a Self::Ty {
        assert!(*self > *arg);
        arg
    }
}

fn use_lifetime_trait<'a>(x: &'a dyn LifetimeTrait<Ty = i32>, y: &'a i32) -> &'a i32 {
    x.lifetime_method(y)
}

pub fn test_function() {
    let x = 42i32;
    let y = 10i32;
    let _result = use_lifetime_trait(&x, &y);
}