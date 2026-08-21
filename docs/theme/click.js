// mdBook renders the table-of-contents toggle as a label for a hidden
// checkbox. Make that visible control operable from the keyboard too.
document.addEventListener("DOMContentLoaded", () => {
    const toggle = document.getElementById("sidebar-toggle");
    if (!toggle) {
        return;
    }

    toggle.tabIndex = 0;
    toggle.setAttribute("role", "button");
    toggle.setAttribute("aria-controls", "sidebar");
    toggle.addEventListener("keydown", (event) => {
        if (event.key !== "Enter" && event.key !== " ") {
            return;
        }
        event.preventDefault();
        toggle.click();
    });
});
