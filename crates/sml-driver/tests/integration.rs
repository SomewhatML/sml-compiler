use goldentests::{TestConfig, TestResult};

#[test]
#[cfg(target_family = "windows")]
fn goldentests() -> TestResult<()> {
    let config = TestConfig::new("../../target/debug/sml-driver.exe", "../../tests/", "-- ")?;
    config.run_tests()
}

#[test]
#[cfg(target_family = "unix")]
fn goldentests() -> TestResult<()> {
    let config = TestConfig::new("../../target/debug/sml-driver", "../../tests/", "-- ")?;
    config.run_tests()
}
