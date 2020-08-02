use goldentests::{TestConfig, TestResult};

#[test]
fn goldentests() -> TestResult<()> {
    let config = TestConfig::new("../../target/debug/sml-driver.exe", "../../tests/", "-- ")?;
    config.run_tests()
}
