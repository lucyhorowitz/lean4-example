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
    # create AST node
    node_id = str(uuid.uuid4())
    print("creating ASTNode(kind={}, id={})".format(node_dict.get("kind"), node_id))
    tx.run(
        "CREATE (n:ASTNode {id: $id, kind: $kind, info: $info})",
        id=node_id,
        kind=node_dict.get("kind"),
        info=node_dict.get("info")
    )
    # link to parent
    if parent_id:
        tx.run(
            "MATCH (p:ASTNode {id: $parent_id}), (n:ASTNode {id: $id}) "
            "CREATE (p)-[:HAS_ARG]->(n)",
            parent_id=parent_id, id=node_id
        )
    # recurse into arguments
    for arg in node_dict.get("args", []):
        if "node" in arg and arg["node"]:
            create_node(tx, arg["node"], parent_id=node_id)
        elif "atom" in arg:
            leaf = arg["atom"]
            leaf_id = str(uuid.uuid4())
            tx.run(
                "CREATE (l:ASTToken {id: $id, type: 'atom', val: $val})",
                id=leaf_id,
                val=leaf.get("val")
            )
            tx.run(
                "MATCH (p:ASTNode {id: $parent_id}), (l:ASTToken {id: $id}) "
                "CREATE (p)-[:HAS_TOKEN]->(l)",
                parent_id=node_id, id=leaf_id
            )
        elif "ident" in arg:
            leaf = arg["ident"]
            leaf_id = str(uuid.uuid4())
            tx.run(
                "CREATE (l:ASTToken {id: $id, type: 'ident', val: $val})",
                id=leaf_id,
                val=leaf.get("val")
            )
            tx.run(
                "MATCH (p:ASTNode {id: $parent_id}), (l:ASTToken {id: $id}) "
                "CREATE (p)-[:HAS_TOKEN]->(l)",
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
