use super::c_frontend::parse_c_source_unit;
use super::*;
use crate::kernel::CTypedAccessPolicy;

fn source_output(body: &str, initialized: bool, native_profile: bool) -> Result<(), String> {
    let c_source = format!(
        "struct byte_span {{ unsigned char* data; unsigned int count; }}; void fill_span(struct byte_span out) {{ {body} }} unsigned int span_word(void) {{ unsigned int value; struct byte_span out; out.data = (unsigned char*)(void*)&value; out.count = 4; fill_span(out); return value; }}"
    );
    let guarantee = if initialized {
        "ensures initialized(out.data[0..4]);"
    } else {
        ""
    };
    let click = format!(
        "verifying \"span_output.c\"; void fill_span(struct byte_span out) {{ owns out.data[0..4]; {guarantee} }} by {{ execute(); simp(); }} uint32 span_word() {{ ensures result == result; }} by {{ execute(); simp(); }}"
    );
    if !native_profile {
        return verify_c0_sources(&click, &[("span_output.c", c_source.as_str())])
            .map(|_| ())
            .map_err(|error| format!("{error:?}"));
    }
    // The body and contracts are unchanged. This explicit typed-frontend
    // fixture selects native geometry independently of byte ownership.
    let sources = CSourceContext::bundle(&[("span_output.c", c_source.as_str())]);
    let mut unit = parse_c_source_unit("span_output.c", &sources, CTarget::SUPPORTED)
        .map_err(|error| format!("{error:?}"))?;
    unit.functions = unit
        .functions
        .into_iter()
        .map(|parsed| {
            let parsed = parsed
                .with_native_parameter_inputs_for_test()
                .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
            let kernel = parsed.to_kernel_function();
            parsed.with_prelowered_kernel_function(kernel)
        })
        .collect();
    sources
        .parsed_units
        .borrow_mut()
        .insert("span_output.c".into(), Arc::new(unit));
    verify_c0_sources_with_context(&click, &sources, None, None, None, None)
        .map(|_| ())
        .map_err(|error| format!("{error:?}"))
}

#[test]
fn native_profile_by_value_output_complete_writes_verify_inline_and_modular() {
    source_output(
        "out.data[0]=1; out.data[1]=2; out.data[2]=3; out.data[3]=4;",
        true,
        true,
    )
    .expect("explicit four-byte output initializes caller's word");
}

#[test]
fn by_value_output_noop_and_hole_cannot_claim_initialization() {
    for body in ["", "out.data[0]=1; out.data[1]=2; out.data[3]=4;"] {
        assert!(source_output(body, true, true).is_err());
    }
}

#[test]
fn by_value_output_ownership_without_explicit_guarantee_does_not_initialize() {
    assert!(source_output("", false, true).is_err());
}

#[test]
fn reassigned_descriptor_cannot_initialize_its_frozen_original_target() {
    assert!(source_output("unsigned char other[4]; out.data=other; out.data[0]=1; out.data[1]=2; out.data[2]=3; out.data[3]=4;", true, true).is_err());
}
#[test]
fn plain_c_byte_ownership_does_not_supply_native_output_geometry() {
    assert!(
        source_output(
            "out.data[0]=1; out.data[1]=2; out.data[2]=3; out.data[3]=4;",
            true,
            false
        )
        .is_err()
    );
}
