# The Gold language

The Gold language is a programmable configuration language. Gold serves as an
alternative to other configuration languages, such as
[JSON](https://www.json.org/json-en.html),
[YAML](https://yaml.org/),
[TOML](https://toml.io/en/)
and others, by providing access to conventional programming language features
such as functions, loops, imports and data sharing. By doing this Gold occupies the same niche as languages like
[Dhall](https://dhall-lang.org/).
Gold offers the following features distinct from Dhall:

- a more familiar syntax,
- a less constraining type system, and
- first class support for functions.

The final point means that functions are valid as output values from Gold programs. This means that conditions which must be expressed in e.g. Github Actions YAML files as text:

```yaml
jobs:
  production-deploy:
    if: github.repository == 'octo-org/octo-repo-prod'
```

can be written in Gold in a more natural way

```
{
  jobs: {
    production-deploy: {
      if: |github| github.repository == "octo-org/octo-repo-prod"
    }
  }
}
```

(In Gold, curly braces define objects, that is, string-value mappings, while the
pipe character defines a function.) Here, the value of the `if` field is a true
function to be called by the host application, not a string to be interpreted in
whichever mini-language applies for this particular key (which is of course a
different mini-language from other keys that need similar features.)

This feature of first-class functions was integral to the original motivation
for creating the Gold language.
