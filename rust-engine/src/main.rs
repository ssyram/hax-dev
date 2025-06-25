use hax_rust_engine::{
    ast::{span::Span, Item},
    lean::Lean,
    ocaml_engine::{ExtendedToEngine, Response},
    printer::Allocator,
};
use hax_types::engine_api::File;

use pretty::{DocAllocator, DocBuilder};

fn krate_name(items: &Vec<Item>) -> String {
    let head_item = items.get(0).unwrap();
    head_item.ident.krate()
}

fn main() {
    let ExtendedToEngine::Query(input) = hax_rust_engine::hax_io::read() else {
        panic!()
    };
    let (value, _map) = input.destruct();

    let query = hax_rust_engine::ocaml_engine::Query {
        hax_version: value.hax_version,
        impl_infos: value.impl_infos,
        kind: hax_rust_engine::ocaml_engine::QueryKind::ImportThir { input: value.input },
    };

    let Some(Response::ImportThir { output: items }) = query.execute() else {
        panic!()
    };

    // Special hook to use the engine for generating `names/generated.rs`.
    if let Ok(path) = std::env::var("HAX_RUST_ENGINE_GENERATE_NAMES") {
        let file = hax_rust_engine::names::codegen::export_def_ids_to_mod(items);
        std::fs::write(path, file).expect("Unable to write file");
        return;
    }

    let krate = krate_name(&items);

    // For now, the main function always calls the Lean backend
    let allocator = Allocator::new(Lean);

    let header = allocator
        .intersperse(
            vec![
            "-- Experimental lean backend for Hax",
            "-- Comment the following line to not import the prelude (requires the Lib.lean file) : ",
            "import Lib",
        ],
            allocator.hardline(),
        )
        .append(allocator.hardline())
        .append(allocator.hardline());

    let item_docs: DocBuilder<_, Span> = header.append(allocator.intersperse(
        items.iter(),
        allocator.hardline().append(allocator.hardline()),
    ));

    hax_rust_engine::hax_io::write(&hax_types::engine_api::protocol::FromEngine::File(File {
        path: krate + ".lean",
        contents: item_docs.pretty(80).to_string(),
        sourcemap: None,
    }));
}
