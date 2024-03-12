import Lean
import Verbose.Infrastructure.WidgetM
import Verbose.Infrastructure.SelectionInfo

open Lean Elab Command Term Meta

instance : ToString NameSet :=
  ⟨fun n ↦ n.toList.map toString |> toString⟩

/-! ## SingleValPersistentEnvExtension -/

/-- A persistent environment extension that is meant to hold a single (mutable) value. -/
def SingleValPersistentEnvExtension (α : Type) := PersistentEnvExtension α α α

instance {α} [Inhabited α] : Inhabited (SingleValPersistentEnvExtension α) :=
  inferInstanceAs <| Inhabited  <| PersistentEnvExtension α α α

def registerSingleValPersistentEnvExtension (name : Name) (α : Type) [Inhabited α] : IO (SingleValPersistentEnvExtension α) :=
  registerPersistentEnvExtension {
    name            := name,
    mkInitial       := pure default,
    addImportedFn   := mkStateFromImportedEntries (fun _ b => return b) (return default),
    addEntryFn      := (λ _ b => b),
    exportEntriesFn := λ x => #[x]
  }

variable {m: Type → Type} [Monad m] [MonadEnv m] {α : Type} [Inhabited α]

def SingleValPersistentEnvExtension.get (ext : SingleValPersistentEnvExtension α) : m α :=
  return ext.getState (← getEnv)

def SingleValPersistentEnvExtension.set (ext : SingleValPersistentEnvExtension α) (a : α) : m Unit := do
  modifyEnv (ext.modifyState · (λ _ => a))

/-! ## Declaration names extensions infrastructure -/

abbrev NameListDict := RBMap Name (List Name) Name.quickCmp

abbrev DeclListExtension := SimplePersistentEnvExtension (Name × List Name) NameListDict

def  DeclListExtension.defineDeclList (ext : DeclListExtension)
    (name : Ident) (args : Array Ident) :
    CommandElabM Unit := do
  let env ← getEnv
  let sets := ext.getState env
  if sets.contains name.getId then
    throwError "There is already a declaration list named {name}."
  let mut entries : List Name := []
  for arg in args do
    let argN := arg.getId
    if (env.find? argN).isSome then
      entries := entries.insert argN
    else if let some set := sets.find? argN then
      entries := entries ++ set
    else
      throwError "Could not find a declaration or declaration list named {argN}."
  modifyEnv (ext.addEntry · (name.getId, entries))

macro "registerDeclListExtension" name:ident : command =>
`(initialize $name : DeclListExtension ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map ⟨key, val⟩ ↦ map.insert key val
    addImportedFn := fun as ↦ .fromArray (as.concatMap id) Name.quickCmp
  })

def  DeclListExtension.printDeclList (ext : DeclListExtension) : CommandElabM Unit :=
  for entry in ext.getState (← getEnv) do
    IO.println s!"{entry.1} : {entry.2}"

def DeclListExtension.gatherNames (ext : DeclListExtension) (args : Array Ident)
    (expectedType? : Option Expr := none) : CommandElabM (Array Name) := do
  let mut result : Array Name := #[]
  let env ← getEnv
  let sets := ext.getState env
  let checkName (name : Name) : CommandElabM (Option Name) := do
    let names ← try
        resolveGlobalConstCore name
      catch _ => return none
    if names.length > 1 then
      throwError "The name {name} is ambiguous: possible interpretations are {names}"
    else if names.isEmpty then
      return none
    let name := names[0]!
    if let some info := env.find? name then
      if let some expectedType := expectedType? then
        unless ← liftTermElabM <| isDefEq info.type expectedType do
          let expectedFmt ← liftTermElabM <| ppExpr expectedType
          throwError "The type {info.type} of {name} is not suitable: expected {expectedFmt}"
      return name
    else
      return none
  for arg in args do
    let argN := arg.getId
    if let some name ← checkName argN then
      result := result.push name
    else if let some set := sets.find? argN then
      for name in set do
        if let some name ← checkName name then
          result := result.push name
        else
          throwError "Could not find a declaration or declaration list named {name}."
    else
      throwError "Could not find a declaration or declaration list named {argN}."
  return result



/-! ##  Suggestions provider lists extension -/

registerDeclListExtension suggestionsProviderListsExt

/-- Print all registered suggestions provider lists for debugging purposes. -/
elab "#suggestions_provider_lists" : command => do
  suggestionsProviderListsExt.printDeclList

/-- Register a list of suggestions providers. -/
elab "SuggestionProviderList" name:ident ":=" args:ident* : command =>
  suggestionsProviderListsExt.defineDeclList name args

abbrev SuggestionProvider := SelectionInfo → MVarId → WidgetM Unit


/-! ##  Anonymous split lemmas lists extension -/

registerDeclListExtension anonymousSplitListsExt

/-- Print all registered anonymous split lemmas lists for debugging purposes. -/
elab "#anonymous_split_lemmas_lists" : command => do
  anonymousSplitListsExt.printDeclList

/-- Register a list of anonymous split lemmas. -/
elab "AnonymousSplitLemmasList" name:ident ":=" args:ident* : command =>
  anonymousSplitListsExt.defineDeclList name args

/-! ##  Anonymous lemmas lists extension -/

registerDeclListExtension anonymousLemmasListsExt

/-- Print all registered anonymous lemmas lists for debugging purposes. -/
elab "#anonymous_lemmas_lists" : command => do
  anonymousLemmasListsExt.printDeclList

/-- Register a list of anonymous lemmas. -/
elab "AnonymousLemmasList" name:ident ":=" args:ident* : command =>
  anonymousLemmasListsExt.defineDeclList name args

/-! ##  Unfoldable definitions lists extension -/

registerDeclListExtension unfoldableDefsListsExt

/-- Print all registered unfoldable definitions lists for debugging purposes. -/
elab "#unfoldable_defs_lists" : command => do
  unfoldableDefsListsExt.printDeclList

/-- Register a list of unfoldable definitions. -/
elab "UnfoldableDefsList" name:ident ":=" args:ident* : command =>
  unfoldableDefsListsExt.defineDeclList name args

/-! ## Verbose configuration -/

structure VerboseConfiguration where
  lang : Name := `en
  suggestionsProviders : Array Name
  anonymousLemmas : Array Name
  anonymousSplitLemmas : Array Name
  unfoldableDefs : Array Name
  deriving Inhabited

instance : ToString VerboseConfiguration where
  toString conf := s!"Language: {conf.lang}\nSuggestions providers: {conf.suggestionsProviders}" ++
    "\nAnonymous lemmas: {conf.anonymousLemmas}\nAnonymous split lemmas: {conf.anonymousSplitLemmas}"

initialize verboseConfigurationExt : SingleValPersistentEnvExtension VerboseConfiguration
  ← registerSingleValPersistentEnvExtension `gameExt VerboseConfiguration

open Elab Term Meta Command

def Verbose.getSuggestionsProviders : MetaM (Array SuggestionProvider) := do
  let conf ← verboseConfigurationExt.get
  let env ← getEnv
  let mut result : Array SuggestionProvider := #[]
  for name in conf.suggestionsProviders do
    if let some info := env.find? name then
      unless ← isDefEq info.type (.const `SuggestionProvider []) do
        throwError "The type {info.type} of {name} is not suitable: expected SuggestionProvider"
      result := result.push (← unsafe evalConst SuggestionProvider name)
    else
      throwError "Could not find declaration {name}"
  return result

def Verbose.setSuggestionsProviders (suggestionsProviders : Array Name) : m Unit := do
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders := suggestionsProviders}

elab "#print_verbose_config" : command => do
  let conf ← verboseConfigurationExt.get
  IO.println conf

open Elab Term Meta Command

elab "configureSuggestionProviders" args:ident* : command => do
  let providers ← suggestionsProviderListsExt.gatherNames args (some <| .const `SuggestionProvider [])
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with suggestionsProviders := providers}

elab "configureAnonymousLemmas" args:ident* : command => do
  let lemmas ← anonymousLemmasListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousLemmas := lemmas}

elab "configureAnonymousSplitLemmas" args:ident* : command => do
  let lemmas ← anonymousSplitListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with anonymousSplitLemmas := lemmas}

elab "configureUnfoldableDefs" args:ident* : command => do
  let defs ← unfoldableDefsListsExt.gatherNames args
  let conf ← verboseConfigurationExt.get
  verboseConfigurationExt.set {conf with unfoldableDefs := defs}
