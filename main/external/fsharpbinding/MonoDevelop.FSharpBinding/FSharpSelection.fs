namespace MonoDevelop.FSharp

open MonoDevelop
open MonoDevelop.Components.Commands
open MonoDevelop.Core
open MonoDevelop.Ide
open MonoDevelop.Ide.Editor
open Mono.TextEditor
open ExtCore.Control
open Microsoft.FSharp.Compiler
open Microsoft.FSharp.Compiler.Range
open Microsoft.FSharp.Compiler.Ast
open Microsoft.FSharp.Compiler.PrettyNaming
open Microsoft.FSharp.Compiler.SourceCodeServices
open Microsoft.FSharp.Compiler.SourceCodeServices.AstTraversal

type ExpandSelectionHandler() =
    inherit CommandHandler()

    let overlaps (symbolRange, selection:Text.ISegment) =
        let symbolStart, symbolEnd = symbolRange
        symbolStart < selection.EndOffset && selection.Offset < symbolEnd

    let biggerOverlap (symbolRange, selection:Text.ISegment) =
        let symbolStart, symbolEnd = symbolRange
        symbolStart < selection.Offset && symbolEnd >= selection.EndOffset
        ||
        symbolStart <= selection.Offset && symbolEnd > selection.EndOffset

    let inside (symbolRange, selection:Text.ISegment) =
        let symbolStart, symbolEnd = symbolRange
        symbolStart >= selection.EndOffset// && symbolEnd <= selection.EndOffset
    /// Walk over a pattern - this is for example used in 
    /// let <pat> = <expr> or in the 'match' expression
    let rec visitPattern synPat = 
        seq {
            match synPat with
            | SynPat.Wild(range) -> 
                //printfn "  .. underscore pattern"
                yield range
            | SynPat.Named(pat, name, _, _, range) ->
                yield! visitPattern pat
                yield range
                //printfn "  .. named as '%s'" name.idText

            | SynPat.LongIdent(LongIdentWithDots(ident, _), _, _, _, _, range) ->
                //let names = String.concat "." [ for i in ident -> i.idText ]
                //printfn "  .. identifier: %s" names
                yield range
            
            | pat -> //printfn "  .. other pattern: %A" pat
                     yield pat.Range
        }

    /// Walk over an expression - if expression contains two or three 
    /// sub-expressions (two if the 'else' branch is missing), let expression
    /// contains pattern and two sub-expressions
    let rec visitExpression synExpr =
        seq {
            match synExpr with

            | SynExpr.IfThenElse(cond, trueBranch, falseBranchOpt, _, _, _, range) ->
                // Visit all sub-expressions
               // printfn "Conditional:"
                yield! visitExpression cond
                yield! visitExpression trueBranch
            
                if falseBranchOpt.IsSome then
                    yield! visitExpression falseBranchOpt.Value
                    yield falseBranchOpt.Value.Range
                yield range
            | SynExpr.LetOrUse(_, _, bindings, body, range) ->
                // Visit bindings (there may be multiple 
                // for 'let .. = .. and .. = .. in ...'
                //printfn "LetOrUse with the following bindings:"
                for binding in bindings do
                    let (Binding(_access, _kind, _inlin, _mutabl, _attrs, _xmlDoc, 
                                 _data, pat, _retInfo, init, _m, _sp)) = binding
                    yield! visitPattern pat 
                    yield! visitExpression init
                    yield range
                // Visit the body expression
                //printfn "And the following body:"
                yield! visitExpression body
                yield range
            | SynExpr.Match(_,_,_,_,range) -> yield range
            | SynExpr.MatchLambda(_,_,_,_,range) -> yield range
            //| SynExpr.tr
            //| SynExpr.
            | expr -> //printfn " - not supported expression: %A" expr
                      yield expr.Range
          }

    /// Walk over a list of declarations in a module. This is anything
    /// that you can write as a top-level inside module (let bindings,
    /// nested modules, type declarations etc.)
    let rec visitDeclarations decls = 
        seq {
            for declaration in decls do
                match declaration with
                | SynModuleDecl.Let(_isRec, bindings, range) ->
                    // Let binding as a declaration is similar to let binding
                    // as an expression (in visitExpression), but has no body
                    for binding in bindings do
                        let (Binding(_access, _kind, _inlin, _mutabl, _attrs, _xmlDoc, 
                                     _data, pat, _retInfo, body, _m, _sp)) = binding
                        yield! visitPattern pat 
                        yield! visitExpression body
                        yield range
                | SynModuleDecl.NestedModule(_,decls,_, range) ->
                    yield! visitDeclarations decls
                    yield range
                //| SynModuleDecl.Types(typeDefns, range) ->
                //    yield! visitTypeDefinitions typeDefns
                //    yield range
                | _ -> //printfn " - not supported declaration: %A" declaration
                       yield declaration.Range
        }

    /// Walk over all module or namespace declarations 
    /// (basically 'module Foo =' or 'namespace Foo.Bar')
    /// Note that there is one implicitly, even if the file
    /// does not explicitly define it..
    let visitModulesAndNamespaces modulesOrNss =
        seq {
            for moduleOrNs in modulesOrNss do
                let (SynModuleOrNamespace(lid, _isMod, decls, _xml, _attrs, _, range)) = moduleOrNs
                printfn "Namespace or module: %A" lid
                yield! visitDeclarations decls
                yield range
        }

    let getParseTree() =
        maybe {
            let! doc = IdeApp.Workbench.ActiveDocument |> Option.ofObj
            let editor = doc.Editor
            let projectFile = doc.Project.FileName.ToString()
            let parseFileResults = languageService.ParseFileInProject(projectFile, doc.FileName.ToString(), doc.Editor.Text) |> Async.RunSynchronously

            //let checker = FSharpChecker.Create()
            //  // Get compiler options for the 'project' implied by a single script file
            //let projOptions = 
            //    checker.GetProjectOptionsFromScript(doc.FileName.ToString(), doc.Editor.Text)
            //    |> Async.RunSynchronously

            //// Run the first phase (untyped parsing) of the compiler
            //let parseFileResults = 
            //    checker.ParseFileInProject(doc.FileName.ToString(), doc.Editor.Text, projOptions) 
            //    |> Async.RunSynchronously

            return! parseFileResults.ParseTree
        }
    override x.Update(info:CommandInfo) =

        LoggingService.logDebug "enabled"
        info.Enabled <- true

    override x.Run() =

        LoggingService.logDebug "got here"
        let tree =
            maybe {
                let! doc = IdeApp.Workbench.ActiveDocument |> Option.ofObj
                //let! ast = doc.TryGetAst()
                //let! tree = ast.ParseTree
                let! tree = getParseTree()
                //let! syms = ast.GetAllUsesOfAllSymbolsInFile() |> Async.RunSynchronously
                //syms |> Seq.iter (fun s -> printf "%A" s.RangeAlternate)
                //let! parseResults = ast.CheckResults
                let editor = doc.Editor
                let lineInfo = editor.GetLineInfoByCaretOffset ()
                //let symbol = ast.GetSymbolAtLocation lineInfo |> Async.RunSynchronously
                //let loc  = .OffsetToLocation(offset)
                //let line, col = max loc.Line 1, loc.Column - 1
                //LoggingService.logDebug "%A" tree
                //let! pd = doc.ParsedDocument |> Option.tryCast<FSharpParsedDocument>
                //let syms = pd.AllSymbolsKeyed
                let selection = doc.Editor.SelectionRange


                if not doc.Editor.IsSomethingSelected then
                    //doc.Editor.OffsetToLocation selection.Offset
                    let line = editor.GetLine editor.CaretLine
                    if editor.CaretColumn = line.LengthIncludingDelimiter || editor.CaretOffset = line.Offset then
                        editor.SetSelection(line.Offset, line.EndOffset)
                    else
                        let data = doc.Editor.GetContent<ITextEditorDataProvider>().GetTextEditorData()
                        editor.SetSelection (data.FindCurrentWordStart(editor.CaretOffset), data.FindCurrentWordEnd(editor.CaretOffset))
                else

                    //doc.Editor.CaretLocation
            //let pos = mkPos selStart.Line (selStart.Column - 1)
                    let pos = mkPos editor.CaretLine (editor.CaretColumn - 1)
                    let rangeAsOffsets(range:Range.range) =
                        let startPos = editor.LocationToOffset(range.StartLine, range.StartColumn + 1)
                        let endPos = editor.LocationToOffset(range.EndLine, range.EndColumn + 1)
                        (startPos, endPos)

                    let rec walker = 
                        { new AstTraversal.AstVisitorBase<_>() with
                            member this.VisitExpr(path, traverseSynExpr, defaultTraverse, expr) =
                                let path, traverseSynExpr, expr = path, traverseSynExpr, expr
                                //defaultTraverse(expr)
                                //Some expr.Range }
                                //if rangeContainsPos expr.Range pos && not(biggerOverlap(rangeAsOffsets expr.Range, doc.Editor.SelectionRange)) then
                                if inside(rangeAsOffsets expr.Range, doc.Editor.SelectionRange) then
                                    LoggingService.logDebug "Found range %A" expr.Range
                                    Some path
                                    //match TryGetExpression false expr with
                                    //| (Some parts) -> parts |> String.concat "." |> Some
                                    //| _ -> defaultTraverse(expr)
                                else
                                    defaultTraverse(expr) }
                    let nodesOpt = AstTraversal.Traverse(mkPos editor.CaretLine editor.CaretColumn, tree, walker)

                    //LoggingService.logDebug "%A" nodesOpt
                    //nodesOpt 
                    //|> Option.iter (fun range ->
                    //    let startPos, endPos = rangeAsOffsets range
                    //    editor.SetSelection(startPos, endPos))
                    let rangeFromTraverse = function
                        | TraverseStep.Binding(binding) -> binding.RangeOfHeadPat
                        | TraverseStep.MatchClause(synMatchClause) -> synMatchClause.Range
                        | TraverseStep.Expr synExpr -> synExpr.Range
                          // MatchClause(SynMatchClause) 
                        | TraverseStep.MemberDefn synMemberDefn -> synMemberDefn.Range
                        | TraverseStep.Module synModuleDecl -> synModuleDecl.Range
                        | TraverseStep.ModuleOrNamespace synModuleOrNamespace -> synModuleOrNamespace.Range
                        | TraverseStep.TypeDefn synTypeDefn -> synTypeDefn.Range

                    nodesOpt 
                    |> Option.iter (fun nodes -> 
                                        let node = 
                                            nodes 
                                            |> List.map rangeFromTraverse
                                            |> Seq.map rangeAsOffsets
                                            |> Seq.filter (fun range -> biggerOverlap(range, doc.Editor.SelectionRange))
                                            |> Seq.sortBy (fun (startPos, endPos) -> endPos - startPos)
                                            |> Seq.tryHead

                                        match node with
                                        | Some (startPos, endPos) -> doc.Editor.SetSelection(startPos, endPos)
                                        | _ -> LoggingService.logDebug "Did not find a region to expand the selection to")
                                        //let startPos, endPos = node
                                        //editor.SetSelection(startPos, endPos))
                    //let lastNode = nodes |> List.tail |> List.tryHead
                    //|> Seq.iter (fun sym -> LoggingService.logDebug "%A %A" sym.RangeAlternate sym.Symbol.DisplayName)
                    //FSharpNoteworthyParamInfoLocations.Find(
                    // Extract implementation file details
                    //match tree with
                    //| ParsedInput.ImplFile(implFile) ->
                    //    // Extract declarations and walk over them
                    //    let (ParsedImplFileInput(fn, script, name, _, _, modules, _)) = implFile
                    //    //LoggingService.logDebug "%A" modules
                    //    let ranges = visitModulesAndNamespaces modules |> List.ofSeq
                    //    //ranges |> Seq.iter (fun r -> printfn "(%d - %d) - (%d - %d)" r.StartLine r.StartColumn r.EndLine r.EndColumn )

                    //    LoggingService.logDebug "%A" editor.SelectionRange
                    //    let smallestOverlapRange =
                    //        ranges
                    //        |> Seq.map rangeAsOffsets

                    //        |> Seq.filter (fun range -> biggerOverlap(range, doc.Editor.SelectionRange))
                    //        |> Seq.map(fun (startPos, endPos) -> LoggingService.logDebug "%d %d" startPos endPos
                    //                                             (startPos, endPos))
                    //        |> Seq.sortBy (fun (startPos, endPos) -> endPos - startPos)
                    //        |> Seq.tryHead
        
                    //    match smallestOverlapRange with
                    //    | Some (startPos, endPos) -> ()//doc.Editor.SetSelection(startPos, endPos)
                    //    | _ -> LoggingService.logDebug "Did not find a region to expand the selection to"
                    //| _ -> failwith "F# Interface file (*.fsi) not supported."        
            }
        ()