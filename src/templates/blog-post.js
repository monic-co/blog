import React from 'react'
import Helmet from 'react-helmet'
import Link from 'gatsby-link'
import get from 'lodash/get'
import rehypeReact from "rehype-react";
import loadLanguages from 'prismjs/components/index.js'
loadLanguages(['lisp']);

import AnnotatedCode from '../components/AnnotatedCode'
import Bio from '../components/Bio'

const renderAst = new rehypeReact({
  createElement: React.createElement,
  components: { "annotated-code": AnnotatedCode },
}).Compiler;

class BlogPostTemplate extends React.Component {
  render() {
    const {data,pathContext} = this.props
    const post = data.markdownRemark
    const siteTitle = get(data, 'site.siteMetadata.title')
    const { previous, next } = pathContext

    return (
      <div
        style={{
          marginBottom: 200,
        }}>
        <Helmet title={`${post.frontmatter.title} | ${siteTitle}`} />
        <h1>{post.frontmatter.title}</h1>
        <p
          style={{
            display: 'block',
            marginBottom: '50px',
          }}
        >
          {post.frontmatter.date}
        </p>
        {renderAst(post.htmlAst)}
        <hr
          style={{
            backgroundColor: '#0a2e6b',
            margin: '30px 0',
            height: '1px',
            border: 'none',
          }}
        />
        <Bio />

        <ul
          style={{
            display: 'flex',
            flexWrap: 'wrap',
            justifyContent: 'space-between',
            listStyle: 'none',
            padding: 0,
          }}
        >
          {previous && (
            <li>
              <Link to={previous.fields.slug} rel="prev">
                ← {previous.frontmatter.title}
              </Link>
            </li>
          )}

          {next && (
            <li>
              <Link to={next.fields.slug} rel="next">
                {next.frontmatter.title} →
              </Link>
            </li>
          )}
        </ul>
      </div>
    )
  }
}

export default BlogPostTemplate

export const pageQuery = graphql`
  query BlogPostBySlug($slug: String!) {
    site {
      siteMetadata {
        title
        author
      }
    }
    markdownRemark(fields: { slug: { eq: $slug } }) {
      id
      htmlAst
      frontmatter {
        title
        date(formatString: "MMMM DD, YYYY")
      }
    }
  }
`
