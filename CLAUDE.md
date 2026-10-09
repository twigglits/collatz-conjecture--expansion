# CLAUDE.md

## Version control restrictions

Claude must **not** perform any write operations to git or GitHub repositories. The user is the only one allowed to manage version control. Specifically:

## Plugins
When referencing documentation for AWS / Terraform , always do it through
your plugins and / or MCP connection to AWS / Terraform docs respetively.

- **NEVER** set yourself ( Claude ) as the author on a git commit. I, Jean Naude, jean@overdrive.co.za  am the author of any and all commits.
- **Do NOT** run `git add`, `git commit`, or `git push`.
- **Do NOT** run any other command that modifies repository or remote state (e.g. `git merge`, `git rebase`, `git reset`, `git tag`, `git stash`, `git cherry-pick`, force-pushes, or GitHub write operations via `gh`/the API such as creating PRs, merging, or pushing branches).
- In **exception** cases where I do give you explicit consent to git commit changes, 

Claude **is** allowed to perform read-only git operations, including:

- Reading files in the working tree.
- Inspecting history and state: `git status`, `git log`, `git diff`, `git show`, `git blame`.
- Reading branches, tags, and remote refs: `git branch`, `git fetch` (read-only refresh), `git remote -v`, `git ls-remote`.

## Coding Development

When the user asks in which files certain functions , components or other references are made. Claude must always find the path to that file containing the relevant information, and output the path relative to directory of the CLAUDE.md file. 

If a task would require a write operation to version control, Claude should stop and ask the user to perform it themselves, or prepare the changes and let the user handle the `add`/`commit`/`push`.

## Context summary artifacts

When the user asks Claude to generate any image, diagram, picture, or report whose purpose is to explain the codebase or its components, Claude must write the output to the `springhare-context-summary/` directory at the root of this workspace (the directory that contains this CLAUDE.md). Create the directory if it does not already exist, and keep any diagram-as-code source (e.g. `.dot`, `.mmd`) alongside the rendered image in that same directory. This keeps explanatory material out of the code repositories.
