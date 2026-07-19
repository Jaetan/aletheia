// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

//! Bundle-consumer fixture (Rust): drives the shared release-bundle scenario
//! through the bundled crate — env-constructor (`Client::new` resolves the
//! shared library through the `ALETHEIA_LIB` seam set by the bundle's env.sh),
//! `parse_dbc_text` of a real `.dbc`, an `Always(VehicleSpeed < 100)` LTL
//! property, one conforming and one violating frame, exactly one violation on
//! the expected property, `end_stream`.  Built by tools/bundle_validate.py
//! with the path dependency printed by the bundle's install.sh substituted
//! into Cargo.toml verbatim.

use std::process::ExitCode;

use aletheia::{
    CanId, Client, Dlc, Formula, FrameResponse, Predicate, Rational, Timestamp, Verdict,
};

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    let [_, dbc_path] = args.as_slice() else {
        return Err("usage: consumer <scenario-dbc-path>".to_string());
    };
    let text = std::fs::read_to_string(dbc_path).map_err(|e| format!("read {dbc_path}: {e}"))?;

    // Env-constructor: resolves the shared library through ALETHEIA_LIB.
    let client = Client::new().map_err(|e| format!("Client::new: {e}"))?;

    let parsed = client
        .parse_dbc_text(&text)
        .map_err(|e| format!("parse_dbc_text: {e}"))?;
    if parsed.dbc.messages.len() != 2 {
        return Err("vehicle.dbc should carry the VehicleDynamics + BrakeStatus messages".into());
    }

    // Always(VehicleSpeed < 100 kph).
    let prop = Formula::Always(Box::new(Formula::Atomic(Predicate::LessThan {
        signal: "VehicleSpeed".to_string(),
        value: Rational::integer(100),
    })));
    client
        .set_properties(&[prop])
        .map_err(|e| format!("set_properties: {e}"))?;
    client
        .start_stream()
        .map_err(|e| format!("start_stream: {e}"))?;

    let id = CanId::standard(256).map_err(|e| format!("CanId: {e}"))?;
    let dlc = Dlc::new(8).map_err(|e| format!("Dlc: {e}"))?;

    // Conforming frame: VehicleSpeed raw 0x1388 (5000) -> 50.00 kph (factor 0.01).
    let ack = client
        .send_frame(
            Timestamp(1000),
            id,
            dlc,
            &[0x88, 0x13, 0, 0, 0, 0, 0, 0],
            None,
            None,
        )
        .map_err(|e| format!("send_frame (conforming): {e}"))?;
    if !matches!(ack, FrameResponse::Ack) {
        return Err("the conforming frame should be acknowledged without property events".into());
    }

    // Violating frame: VehicleSpeed raw 0x4E20 (20000) -> 200.00 kph, over the bound.
    let resp = client
        .send_frame(
            Timestamp(2000),
            id,
            dlc,
            &[0x20, 0x4E, 0, 0, 0, 0, 0, 0],
            None,
            None,
        )
        .map_err(|e| format!("send_frame (violating): {e}"))?;
    let FrameResponse::Verdicts(results) = resp else {
        return Err("the violating frame should produce property verdicts".into());
    };
    let violations: Vec<_> = results
        .iter()
        .filter(|r| r.verdict == Verdict::Fails)
        .collect();
    let [violation] = violations.as_slice() else {
        return Err("expected exactly one violation from the violating frame".into());
    };
    if violation.property_index != 0 {
        return Err("the violation should name the single installed property".into());
    }
    let Some(enrichment) = &violation.enrichment else {
        return Err("the violation should carry an enrichment".into());
    };
    if !enrichment
        .signals
        .iter()
        .any(|(name, _)| name == "VehicleSpeed")
    {
        return Err("the enrichment should carry the VehicleSpeed value".into());
    }

    client
        .end_stream()
        .map_err(|e| format!("end_stream: {e}"))?;

    println!("BUNDLE-CONSUMER rust: OK — exactly one violation on the expected property");
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("BUNDLE-CONSUMER rust: FAIL — {message}");
            ExitCode::FAILURE
        }
    }
}
