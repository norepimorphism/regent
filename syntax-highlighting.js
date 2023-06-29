function linkStyle(name) {
    var e = document.createElement("link");
    e.setAttribute("rel", "stylesheet");
    e.setAttribute("href", "https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.7.0/styles/" + name + ".min.css");
    document.head.appendChild(e);
}

function getStyle() {
    if (window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches) {
        return "obsidian";
    }
    return "foundation";
}

// Dynamically select a theme based on the color scheme.
linkStyle(getStyle());
// Apply syntax highlighting.
document.addEventListener('DOMContentLoaded', (_) => {
    document.querySelectorAll('pre > code').forEach((e) => {
        if (e.children.length > 0) {
            console.error("code block contains unescaped HTML");
            return;
        }
        // Using `highlight` with a hard-coded language should be a little more efficient than
        // `highlightElement`, which has to perform language detection.
        e.innerHTML = hljs.highlight(e.innerHTML, { language: "rust" }).value;
        e.classList.add("hljs");
        e.classList.add("language-rust");
    });
});
