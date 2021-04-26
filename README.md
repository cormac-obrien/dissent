# dissent

A flexible, zero-copy recursive descent parsing toolkit.

## Introduction

`dissent` provides types and traits that help write lexers and recursive descent
parsers that consume lexed output. Tokens (lexemes) are defined by the `TokenType`
trait, while syntax rules are described by the `Parse` trait.
