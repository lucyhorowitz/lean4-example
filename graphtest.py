#!/usr/bin/env python3
import json
import uuid
import os
from neo4j import GraphDatabase

# configure connection via environment variables or defaults
uri = "bolt://localhost:7687"
user = "neo4j"
password = "12345678"

driver = GraphDatabase.driver(uri, auth=(user, password))

def create_node(tx, node_dict, parent_id=None):
    # MERGE AST node
    node_id = str(uuid.uuid4())
    
    # collect atom properties to add to this node
    atom_val = None
    atom_pos = atom_endPos = atom_leading = atom_trailing = None
    for arg in node_dict.get("args", []):
        if "atom" in arg and arg["atom"]:
            leaf = arg["atom"]
            atom_val = leaf.get("val")
            info_leaf = leaf.get("info")
            if isinstance(info_leaf, dict):
                original_leaf = info_leaf.get("original", {})
                atom_pos = original_leaf.get("pos")
                atom_endPos = original_leaf.get("endPos")
                atom_leading = original_leaf.get("leading")
                atom_trailing = original_leaf.get("trailing")
            break

    # determine node label, override for null-kind nodes with atom
    kind = node_dict.get("kind")
    if kind in ("none", "null") and atom_val is not None:
        kind_label = "Atom"
    else:
        kind_label = kind

    print("creating ASTNode(kind={}, id={})".format(kind_label, node_id))
    info = node_dict.get("info")
    # only include info property if it is not the literal "none"
    include_info = info != "none"
    query = "MERGE (n:`" + kind_label + "` {id: $id"
    if include_info:
        query += ", info: $info"
    pos = endPos = leading = trailing = None
    if isinstance(info, dict):
        original = info.get("original")
        if isinstance(original, dict):
            pos = original.get("pos")
            endPos = original.get("endPos")
            leading = original.get("leading")
            trailing = original.get("trailing")
    if pos:
        query += ", pos: $pos"
    if endPos:
        query += ", endPos: $endPos"
    if leading :
        query += ", leading: $leading"
    if trailing :
        query += ", trailing: $trailing"
    if atom_val is not None:
        query += ", val: $val"
    if atom_pos is not None:
        query += ", pos: $pos"
    if atom_endPos is not None:
        query += ", endPos: $endPos"
    if atom_leading is not None:
        query += ", leading: $leading"
    if atom_trailing is not None:
        query += ", trailing: $trailing"
    query += "})"
    params = {"id": node_id}  # "kind": node_dict.get("kind") can be removed
    if include_info:
        params["info"] = info
    if pos :
        params["pos"] = pos
    if endPos :
        params["endPos"] = endPos
    if leading :
        params["leading"] = leading
    if trailing :
        params["trailing"] = trailing
    if atom_val is not None:
        params["val"] = atom_val
    if atom_pos is not None:
        params["pos"] = atom_pos
    if atom_endPos is not None:
        params["endPos"] = atom_endPos
    if atom_leading is not None:
        params["leading"] = atom_leading
    if atom_trailing is not None:
        params["trailing"] = atom_trailing
    tx.run(query, **params)
    # link to parent
    if parent_id:
        tx.run(
            "MATCH (p {id: $parent_id}), (n {id: $id}) MERGE (p)-[:HAS_ARG]->(n)",
            parent_id=parent_id, id=node_id
        )
    # recurse into arguments
    for arg in node_dict.get("args", []):
        if "node" in arg and arg["node"]:
            create_node(tx, arg["node"], parent_id=node_id)
        if "ident" in arg:
            leaf = arg["ident"]
            leaf_id = str(uuid.uuid4())
            query = "MERGE (l:Ident {id: $id, val: $val"
            info = leaf.get("info")
            pos = endPos = leading = trailing = None
            if isinstance(info, dict):
                original = info.get("original")
                if isinstance(original, dict):
                    pos = original.get("pos")
                    endPos = original.get("endPos")
                    leading = original.get("leading")
                    trailing = original.get("trailing")
            if pos :
                query += ", pos: $pos"
            if endPos :
                query += ", endPos: $endPos"
            if leading :
                query += ", leading: $leading"
            if trailing :
                query += ", trailing: $trailing"
            query += "})"
            params = {"id": leaf_id, "val": leaf.get("val")}
            if pos :
                params["pos"] = pos
            if endPos :
                params["endPos"] = endPos
            if leading :
                params["leading"] = leading
            if trailing :
                params["trailing"] = trailing
            tx.run(query, **params)
            tx.run(
                "MATCH (p {id: $parent_id}), (l {id: $id}) MERGE (p)-[:HAS_TOKEN]->(l)",
                parent_id=node_id, id=leaf_id
            )
        if "atom" in arg and arg["atom"]:
            leaf = arg["atom"]
            val = leaf.get("val")
            # create separate Atom nodes for parentheses/brackets
            if val in ("(", ")", "{", "}", "[", "]"):
                leaf_id = str(uuid.uuid4())
                query = "MERGE (l:Atom {id: $id, val: $val"
                info = leaf.get("info")
                pos = endPos = leading = trailing = None
                if isinstance(info, dict):
                    original = info.get("original", {})
                    pos = original.get("pos")
                    endPos = original.get("endPos")
                    leading = original.get("leading")
                    trailing = original.get("trailing")
                if pos:
                    query += ", pos: $pos"
                if endPos:
                    query += ", endPos: $endPos"
                if leading:
                    query += ", leading: $leading"
                if trailing:
                    query += ", trailing: $trailing"
                query += "})"
                params = {"id": leaf_id, "val": val}
                if pos:
                    params["pos"] = pos
                if endPos:
                    params["endPos"] = endPos
                if leading:
                    params["leading"] = leading
                if trailing:
                    params["trailing"] = trailing
                tx.run(query, **params)
                tx.run(
                    "MATCH (p {id: $parent_id}), (l {id: $id}) MERGE (p)-[:HAS_TOKEN]->(l)",
                    parent_id=node_id, id=leaf_id
                )
    return node_id


def main():
    # load AST JSON
    with open("commandasts.json") as f:
        data = json.load(f)
    # insert each AST into the graph
    with driver.session() as session:
        asts = data.get("commandASTs", [])
        print("loading {} AST trees".format(len(asts)))
        for ast in asts:
            session.write_transaction(create_node, ast.get("node"))
    driver.close()

if __name__ == "__main__":
    main()
