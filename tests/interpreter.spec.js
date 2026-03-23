// @ts-check
import { test, expect } from '@playwright/test';

// 
// Runs interpreter tests via playwright by loading the "test" page and checking all statuses are OK.
// 


test('interpreter-tests', async ({ page }) => {
    await page.goto('http://localhost:3000/test.html?run=0');
    // await page.goto('http://127.0.0.1:8000/test.html?test=simple5&debug=0');
  
    // Expect a title "to contain" a substring.
    await expect(page.getByText('TLA+ Web Interpreter Tests')).toBeVisible();

    // Retrieve all test elements with class 'test-name-link' and extract test names into a list
    const testNameLinks = await page.$$eval('.test-name-link', links => links.map(link => link.textContent.trim()));
    // testNameLinks now contains a list of test name strings, e.g., ["simple5", ...]

    for (const testName of testNameLinks) {
        const url = `http://localhost:3000/test.html?test=${encodeURIComponent(testName)}`;
        await page.goto(url);

        // Wait for page to be loaded
        await expect(page.getByText('TLA+ Web Interpreter Tests')).toBeVisible();

        // Wait until the test status cell for this test contains 'Done'
        await page.waitForFunction((name) => {
            const td = document.querySelector(`td#test_status-${name}`);
            return td && td.textContent && td.textContent.includes("Done");
        }, testName);

        // Optionally, fail immediately if status is a FAIL (for fast feedback)
        const statusText = await page.$eval(`td#test_status-${testName}`, td => td.textContent);
        if (statusText.includes("FAIL")) {
            throw new Error(`Test ${testName} failed: ${statusText}`);
        }
    }
  });