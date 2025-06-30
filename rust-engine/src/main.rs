use hax_rust_engine::{
    ast::{span::Span, Item},
    lean::Lean,
    ocaml_engine::{ExtendedToEngine, Response},
    printer::Allocator,
};
use hax_types::engine_api::File;

use pretty::{DocAllocator, DocBuilder};

fn get_crate_name(items: &Vec<Item>) -> String {
    let head_item = items.get(0).unwrap();
    head_item.ident.get_crate()
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

    let krate = get_crate_name(&items);

    // For now, the main function always calls the Lean backend
    let allocator = Allocator::new(Lean);

    let item_docs: DocBuilder<_, Span> = allocator.intersperse(
        items.iter(),
        allocator.hardline().append(allocator.hardline()),
    );

    hax_rust_engine::hax_io::write(&hax_types::engine_api::protocol::FromEngine::File(File {
        path: krate + ".lean",
        contents: item_docs.pretty(80).to_string(),
        sourcemap: None,
    }));
}
