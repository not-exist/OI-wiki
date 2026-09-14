import fs from "fs";
import util from "util";
import child_process from "child_process";
import chalk from "chalk";
import { HTMLElement } from "node-html-parser";
import fetch from "node-fetch";

import { AuthorsCache, AuthorUserMap, fetchAuthors } from "./authors-cache.js";
import { TaskHandler, log } from "../html-postprocess.js";

const execFileAsync = util.promisify(child_process.execFile);

type CommitLog = { commitDate: Date; authorEmails: string[] };

function parseCommitsLog(log: string): CommitLog[] {
  const commits = log.trim().slice(1).split("\n>");
  return commits.map(commit => {
    const [dateLine, ...emailLines] = commit
      .split("\n")
      .map(line => line.trim())
      .filter(Boolean);
    return {
      commitDate: new Date(dateLine),
      authorEmails: Array.from(new Set(emailLines.map(emailLine => emailLine.slice(1).toLowerCase())))
    };
  });
}

async function readGitCommitsLog(path: string, lineRanges?: [number, number][]): Promise<CommitLog[]> {
  // When line ranges are given, `git log -L <start>,<end>:<file>` only counts the commits
  // touching those lines, i.e. only the contributors of the referenced fragment.
  // Note that `-L` takes the file argument itself, so no `-- <path>` may be passed,
  // and it cannot be combined with `--follow` (file renames are not followed in this mode).
  const pathSpecifier =
    lineRanges && lineRanges.length
      ? lineRanges.map(([start, end]) => `-L "${start},${end}:$FILENAME"`).join(" ")
      : `--follow -- "$FILENAME"`;
  const { stdout: log } = await execFileAsync(
    "bash",
    [
      /*
       * Format:
       *
       * >Date
       * <AuthorEmail
       * <CoAuthorEmail
       * <...
       * >Date
       * <AuthorEmail
       * <...
       */
      /**
       * Regex explanation:
       * - ^((>.+)|(<.+)|  Co-Authored-By: .+?(<.+)>): Matches lines in the `git log` output.
       *   - (>.+): Matches lines starting with '>' (e.g., commit date lines).
       *   - (<.+): Matches lines starting with '<' (e.g., author or co-author email lines).
       *   - (  Co-Authored-By: .+?(<.+)>): Matches 'Co-Authored-By' lines and captures the email in '<>'.
       * - \\2\\3\\4: Replaces the matched line with the content of the second, third, or fourth capture group.
       * - The `pi` flags:
       *   - `p`: Prints the substituted line.
       *   - `i`: Makes the regex case-insensitive.
       */
      "-c",
      `git log '--pretty=format:>%cD%n<%aE%n%w(0,2,2)%b' ${pathSpecifier} | sed -nE 's/^((>.+)|(<.+)|  Co-Authored-By: .+?(<.+)>)/\\2\\3\\4/pi'`
    ],
    {
      env: {
        ...process.env,
        FILENAME: path
      }
    }
  );

  return parseCommitsLog(log);
}

type IncludedCodeFile = {
  /** Path of the code file relative to the repository root */
  path: string;
  /** Snippet section name (`--8<-- "path:section"`); absent when the whole file is included */
  section?: string;
};

/**
 * Find code files included in the article with the snippet syntax, with either whole-file
 * references (`--8<-- "docs/.../file.cpp"`) or snippet section references (`--8<-- "docs/.../file.cpp:section"`).
 */
function findIncludedCodeFiles(markdown: string): IncludedCodeFile[] {
  const seen = new Set<string>();
  const result: IncludedCodeFile[] = [];
  for (const [, rawPath, rawSection] of markdown.matchAll(/--8<--\s*"(docs\/[^"\n:]+?)(?::([^"\n]+?))?"/g)) {
    const path = rawPath.replaceAll("\\", "/");
    const section = rawSection?.trim();
    if (!path.includes("/code/")) continue;
    const key = section ? `${path}\n${section}` : path;
    if (seen.has(key)) continue;
    seen.add(key);
    result.push({ path, section });
  }
  return result;
}

function escapeRegExp(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

/**
 * Resolve a snippet section reference to the 1-based inclusive line range of its content.
 *
 * Following the semantics of pymdownx "Snippet Sections" (and remark-snippet of OI-Wiki-export),
 * the code file is expected to hold marker comments like `--8<-- [start:section]` and
 * `--8<-- [end:section]`, and only the lines strictly between the two markers are included:
 * - when the end marker is missing, the content extends to the end of the file;
 * - when an end marker appears before any start marker, the section is legitimately empty
 *   (returned as a range with `end < start`).
 *
 * Returns `null` when the section does not exist in the file.
 */
function findSnippetSectionLineRange(code: string, section: string): [number, number] | null {
  const markerRegex = new RegExp(`--8<--\\s*\\[\\s*(start|end):\\s*${escapeRegExp(section)}\\s*\\]`);
  const lines = code.split("\n");
  let startIndex = -1; // Index of the start marker line
  for (const [index, line] of lines.entries()) {
    const match = line.match(markerRegex);
    if (!match) continue;
    if (match[1] === "start") {
      if (startIndex === -1) startIndex = index;
      continue;
    }
    if (startIndex === -1) return [1, 0]; // End marker before any start marker: nothing is included
    return [startIndex + 2, index]; // Content is after the start marker and before the end marker (1-based)
  }
  if (startIndex === -1) return null; // Section not found
  // End marker missing: content extends to the end of the file
  // (a trailing newline does not count as a line of its own)
  const lineCount = lines[lines.length - 1] === "" ? lines.length - 1 : lines.length;
  return [startIndex + 2, lineCount];
}

/** Drop empty ranges, then sort and merge overlapping or adjacent ones. */
function mergeLineRanges(ranges: [number, number][]): [number, number][] {
  const sorted = ranges.filter(([start, end]) => start <= end).sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  const merged: [number, number][] = [];
  for (const [start, end] of sorted) {
    const last = merged[merged.length - 1];
    if (last && start <= last[1] + 1) last[1] = Math.max(last[1], end);
    else merged.push([start, end]);
  }
  return merged;
}

/**
 * Read the commit logs of only the referenced snippet sections of a code file,
 * i.e. only count the contributors of the fragments actually included in the article.
 */
async function readGitCommitsLogOfSnippetSections(path: string, sections: string[]): Promise<CommitLog[]> {
  let lineRanges: [number, number][];
  try {
    const code = await fs.promises.readFile(path, "utf8");
    lineRanges = mergeLineRanges(
      sections.map(section => {
        const range = findSnippetSectionLineRange(code, section);
        if (range === null) throw new Error(`snippet section "${section}" not found`);
        return range;
      })
    );
  } catch (error) {
    // Unreachable in a successful site build as pymdownx.snippets runs with `check_paths: true`;
    // fall back to the whole file instead of silently losing all of its contributors.
    log(`Failed to resolve snippet sections of ${chalk.yellow(path)} (${error}), falling back to the whole file`);
    return readGitCommitsLog(path);
  }
  return lineRanges.length ? readGitCommitsLog(path, lineRanges) : [];
}

const GITHUB_REPO = "OI-wiki/OI-wiki";
const AUTHORS_CACHE_URL = `https://raw.githubusercontent.com/${GITHUB_REPO}/authors-cache/authors.json`;
const AUTHORS_EXCLUDED = ["24OI-Bot", "OI-wiki"];

export const taskHandler = new (class implements TaskHandler<AuthorUserMap> {
  async globalInitialize() {
    log("Ensuring full Git history");
    child_process.execSync("(git rev-parse --is-shallow-repository | grep false >/dev/null) || git fetch --unshallow", {
      stdio: "inherit"
    });

    log(`Fetching authors cache from ${chalk.yellow(AUTHORS_CACHE_URL)}`);
    const authorsCache = (await (await fetch(AUTHORS_CACHE_URL)).json()) as AuthorsCache;

    log(`Fetching authors of commits newer than: ${chalk.yellow(authorsCache.latestCommitTime)}`);
    return (await fetchAuthors(authorsCache)).userMap;
  }

  userMap: AuthorUserMap;

  async initialize(userMap: AuthorUserMap) {
    this.userMap = userMap;
  }

  async process(document: HTMLElement) {
    const $ = document.querySelector.bind(document);
    const $$ = document.querySelectorAll.bind(document);

    $("html").setAttribute("lang", "zh-Hans");

    // The path of .md file relative to /docs, starting with a leading "/"
    const sourceFilePath = ($(".page_edit_url").getAttribute("href") || "").split("?ref=")[1];
    if (sourceFilePath) {
      // Set link to git history
      $(".edit_history").setAttribute("href", `https://github.com/${GITHUB_REPO}/commits/master/docs${sourceFilePath}`);

      const commitsLog = await readGitCommitsLog(`docs${sourceFilePath}`);
      let includedCodeFiles: IncludedCodeFile[] = [];
      try {
        const markdown = await fs.promises.readFile(`docs${sourceFilePath}`, "utf8");
        includedCodeFiles = findIncludedCodeFiles(markdown);
      } catch (error) {
        log(`Failed to read source markdown for ${sourceFilePath}: ${error}`);
      }

      // A file referenced as a whole takes precedence over references to its sections
      const wholeFilePaths = new Set(includedCodeFiles.filter(({ section }) => !section).map(({ path }) => path));
      const sectionsByPath = new Map<string, string[]>();
      for (const { path, section } of includedCodeFiles) {
        if (!section || wholeFilePaths.has(path)) continue;
        if (!sectionsByPath.has(path)) sectionsByPath.set(path, []);
        sectionsByPath.get(path)!.push(section);
      }
      const codeFileLogs = await Promise.all([
        ...[...wholeFilePaths].map(path => readGitCommitsLog(path)),
        ...[...sectionsByPath].map(([path, sections]) => readGitCommitsLogOfSnippetSections(path, sections))
      ]);

      // "本页面最近更新"
      const latestDate = new Date(
        commitsLog.map(l => +new Date(l.commitDate)).reduce((latest, current) => Math.max(latest, current))
      );
      $(".facts_modified").textContent =
        latestDate.toLocaleDateString("zh-CN", { timeZone: "Asia/Shanghai", hour12: false }) +
        " " +
        latestDate.toLocaleTimeString("zh-CN", { timeZone: "Asia/Shanghai", hour12: false });

      // "本页面贡献者"
      const authors = Object.entries(
        // Commit count by author
        [
          // From markdown front-matter
          ...$(".page_contributors")
            .textContent.trim()
            .split(",")
            .map(username => `${username.trim()}\ngithub`),
          // From git history
          ...commitsLog
            .concat(...codeFileLogs)
            .flatMap(l => l.authorEmails)
            .filter(email => email in this.userMap)
            .map(
              email =>
                this.userMap[email].githubUsername
                  ? `${this.userMap[email].githubUsername}\ngithub` // GitHub username
                  : `${this.userMap[email].name}\ngit\n${email}` // Git name (when email not linked with GitHub)
            )
        ].reduce<Record<string, number>>((count, author) => {
          if (AUTHORS_EXCLUDED.some(excluded => `${excluded.toLowerCase()}\ngithub` === author.toLowerCase()))
            return count;

          count[author] = (count[author] || 0) + 1;
          return count;
        }, {})
      )
        .sort(([author1, count1], [author2, count2]) => {
          // Sort DESC by commit count
          if (count1 !== count2) return count2 - count1;
          else return author1.toLowerCase() < author2.toLowerCase() ? -1 : 1;
        })
        .map(([author]) => author);
      $(".page_contributors").innerHTML = authors
        .map(author => {
          const [name, type, email] = author.split("\n");
          return type === "github"
            ? `<a href="https://github.com/${name}" target="_blank">${name}</a>`
            : `<a href="mailto:${email}" target="_blank">${name}</a>`;
        })
        .join(", ");
    } else {
      // Pages without source
      $(".edit_history").setAttribute("href", `https://github.com/${GITHUB_REPO}/commits/master`);
      $(".facts_modified").textContent = "无更新";
      $(".page_contributors").textContent = "（自动生成）";
      $(".page_edit_url").setAttribute("href", "#");
    }
  }
})();
